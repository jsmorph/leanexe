# Development Journal

## 2026-08-07: Bounded Filter Composition

The [Demo 5 baseline](demos/demo-5/README.md) took 1,635.679 seconds in Stage 5 and produced a 969-line direct proof after fourteen edited checks.  Its only checked compiler region was the bounded-length dispatch, leaving Codex to derive the input-capacity allocator, filtered-prefix loop invariant, conditional output store, dynamic result length, and empty branch.  The proof journal supplied the exact emitted program decomposition and invariant used to define the shared theorem.

`Project.ProofKit.FixedArrayFilterLt.wrapperProgram_spec` proves the canonical bounded stable filter for arbitrary maximum size and `UInt64` threshold.  The compiler recognizes the corresponding extracted IR and emits `leanexe.array.filter-lt.v1` over the complete function while preserving the nested length-dispatch region.  The JavaScript consumer validates the parameters and function boundary, constructs a checked equality with `wrapperProgram`, selects the semantic theorem, and generates the complete schema-6 artifact starter.

Three controlled reproofs retained the formal specification, source, 1,975-byte WASM, decoded Program, artifact theorem, and heap-reserve boundary.  The deterministic 70-line starter passed its first Lean check unchanged in every run and produced Stage 5 times of 86.795, 90.745, and 95.718 seconds, giving a 90.745-second median and an 8.923-second range.  The median reduces the baseline by 1,544.934 seconds, or 94.5 percent, and independent `leanexegen verify` accepted the first and third final packages.

## 2026-08-07: Artifact Heap-Reserve Precondition

The bounded filter in [Demo 5](demos/demo-5/README.md) exposed a counterexample to the former `RuntimeReady` precondition.  For input `[100]`, the final output is empty, but the compiled `Array.filter` reserves input-sized capacity before testing the element.  At a bump pointer of `2^32 - 56` with 65,536 memory pages, the former final-output bound held while the allocator failed and the artifact trapped.

The formal task now defines `heapReserveBytes : Array UInt64 → Nat` beside `expected`.  `RuntimeReady` retains its final-output representation bounds and adds separate address-space and existing-memory bounds for the stated heap reserve.  The direct artifact proof must establish each allocation premise from this reserve, which keeps the resource assumption reviewable and tied to exact emitted behavior.

Proof-package schema 6 records the expanded formal interface, while verification and controlled reproof preserve the previous declaration checks and proof starter for schemas 3 through 5.  JavaScript protocol tests cover both starter forms, an existing schema-5 Demo 4 package passes independent verification, and the schema-6 Demo 5 package passes the same verification path.  The retained Demo 5 baseline took 1,635.679 seconds in Stage 5 and identifies bounded filter allocation and loop invariants as the next shared proof target.

## 2026-08-03: Reusable WASM Proof Library Plan

The [WASM proof library plan](docs/wasm-proofs.md) inventories the shared arithmetic, memory, control-flow, runtime, and function-portability support already used by the artifact proofs.  It records the current `leanexegen` access gap: generated proof sessions cannot import repository-owned shared modules and receive no checked declaration catalog.  The ordered work adds a stable facade, dependency and identity audits, a checked catalog, feature-directed Pi context, scalar-loop and memory-runtime pilots, and an ongoing two-consumer distillation rule.

## 2026-08-03: `leanexegen` Headless Codex Orchestration

`tools/leanexegen` now owns generation through three tasks using Codex's [noninteractive mode](https://learn.chatgpt.com/docs/non-interactive-mode.md): formal specification, Lean program, and exact-artifact behavioral proof.  Each task uses one temporary workspace, one ephemeral `codex exec` session, and a JSON output schema.  The session edits its candidate and repeats real Lean or compiler checks, after which the outer process repeats the final checks in a separate workspace.

The formal task sees the request and defines `expected : Array UInt64 → Array UInt64`.  The program task sees the request and frozen formal module, while the proof task sees the request, formal module, WAT-derived Talos `Program`, and deterministic artifact-support modules.  The program workspace and every task outcome containing Source are removed after WASM freezes, so the proof task receives neither Source nor the compiler.

The orchestrator appends `${namespace}.FormalSpec.ArtifactSpec : Wasm.Module → Prop` with fixed predicates for the `Array UInt64` memory representation, allocator-ready initial stores, and terminating execution.  Generated Lean check modules require both `expected : Array UInt64 → Array UInt64` and the exact artifact-specification type before accepting the formal task.  `ArtifactResult.artifact_correct` applies that exact declaration directly to the independently decoded, validated, and translated bytes.

Successful packages retain the three accepted sources, Codex version, task summaries and decisions, one-session reports, diagnostics, source hashes, and report hashes.  Independent verification recomputes those hashes, checks the fixed formal declaration, compares the packaged file with the embedded bytes, rebuilds the artifact theorem, and audits its declarations without invoking Codex or LeanExe.  The package also retains the request, samples, host assumptions, tool pins, deterministic artifact support, and its own copy of the WASM bytes.

The proof workspace continues to use Lake 4.31.0's root-workspace `packagesDir` option to share the pinned dependency directory.  The successful dependency diagnostic completed 3,014 jobs through `tools/leanrun`; the earlier incomplete clone without that option consumed 5.5 GB before removal.  A focused Lean diagnostic accepted the fixed `expected` and `ArtifactSpec` declarations with their exact types.

Focused JavaScript tests cover the stable Codex arguments, strict output schema, single-session orchestration, formal-to-program context, proof-context Source exclusion, deterministic artifact result, task-report hashing, package validation, publication rollback, and existing kernel and axiom screens.  They also cover array samples, complete `UInt64` element validation, the `run` command, and optional proof-kit omission.  The earlier external-backend identity smoke tested a superseded path and does not establish the current headless implementation.

A live single-session identity run completed all seven stages on 2026-08-03.  The formal, program, and artifact-proof sessions ran their prescribed checks through `tools/leanrun`, and every final candidate passed the corresponding independent outer check.  The run published 1,042 bytes at SHA-256 `5561719e6bd6b2b56f2ca932ae16a5f6f518b615053bb766d8e473c4add0a725`, observed `18446744073709551615 → 18446744073709551615`, and passed a separate `tools/leanexegen verify` rebuild of `LeanExeGen.GeneratedRd3267f0041708ae6.Artifact.artifact_correct` without Codex or the compiler.

The progress stream now records each stage's UTC start time, retains publication as stage seven, and reports checked samples and the runnable command under stage eight, `Results`.  A second from-scratch prime-factor run completed all eight stages in 7 minutes 39 seconds, published the same 1,348 artifact bytes at SHA-256 `8ef01d38a73edaca6c9098876af4212bf037ff1a14ba69e186b96a884c54cdcf`, and observed `60 → 4`.  Independent verification rebuilt `LeanExeGen.GeneratedRc8c2d9f87deb0758.Artifact.artifact_correct` from the published package in about 60 seconds, without Codex or the compiler.

The repository-root `demos/demo-1/` directory retains the prime-factor walkthrough and its complete standard streams under names that do not repeat the directory name.  It contains byte-identical copies of the generated `FormalSpec.lean`, `Source.lean`, and `Behavior.lean` files as `spec.lean`, `program.lean`, and `proof.lean`.  It also retains the exact 1,348-byte compiled module as `program.wasm` and its 13,421-byte `wasm-tools 1.251.0` rendering as `program.wat`.  The documentation catalog links to `demos/demo-1/README.md`, while the editor backup and lock files beside the former documentation paths remain untouched.

The first live prime-factor run exposed a difference between LeanExe's `report` and `compile` commands.  `report` accepted the generated entry, but `compile` later rejected its local `countFactors` helper as an unsupported declaration.  The program session now performs a scratch compilation after every report, so the same session receives an extraction or emission diagnostic before stage four freezes any bytes.

`workspace-write` prevented a Codex child from connecting to the user systemd bus, and enabling command network access produced an unreliable bus connection.  `leanexegen` now starts the complete Codex session through `tools/leanrun`, which holds the machine-wide lock and applies one constrained cgroup to Codex and its children.  A nested runner verifies the inherited memory and CPU settings before executing its command, avoiding another systemd connection while preserving the resource policy.

The live proof passed before its maximum-`UInt64` sample failed because Wasmtime parses decimal `i64` arguments as signed values.  The sample shim now converts unsigned inputs above `2^63 - 1` to negative signed decimals and converts signed results back to canonical `UInt64` decimals.  The successful retained run exercised the boundary value as `-1` at the Wasmtime command line while recording the logical input and output as `18446744073709551615`.

## 2026-08-03: Clean-Checkout Artifact Proof Inputs

The warm artifact gate depended on twenty ignored `Project/<Case>/Program.lean` files that every translation target and behavioral specification imports.  Those files could not exist in a clone, so the warm result did not establish the documented cold-checkout capability.  The repository no longer ignores those files, tracks all twenty generated execution caches, and requires `cases.json` to correspond bijectively to those cache paths.

The canonical release identity now covers every Lean source under `proofs/talos/lean/Project`, `Project.lean`, the recursive local `LeanExe` import closure, root and proof Lake files, `.gitignore`, all package manifests and binaries, conformance configuration, tool pins, and the twelve local verification drivers.  The collector also requires directly invoked drivers to be executable regular files and rejects a missing or additional `Program.lean` cache.  The kernel scope audit now scans the proof tree and its two local `LeanExe` imports, and the cold command repeats that audit in the detached checkout before setup.

`tools/talos-proof.js check` generates a temporary Talos model and compares it byte-for-byte with the tracked cache before building the specification.  It does not replace a changed cache; `tools/talos-artifact.js prepare` remains the explicit refresh command.  `test/talos_cache.js` checks nonmutating comparison, changed-cache rejection, and explicit refresh, while `test/artifact_identity.js` checks all proof sources, the exact local import closure, twenty program caches, drivers, and canonical hashing.

The expanded identity invalidated the 2026-08-02 warm receipts as intended.  Fresh artifact and conformance gates passed on 2026-08-03 and recorded release-input SHA-256 `3c10b4bef4505c12ab20d9aed037e288940861f45077bf6340d7a8b79f350c4c` over 565 files.  The artifact receipt covers twenty packages, while the conformance receipt covers fifteen invalid modules and twenty-five execution files with the configured imported-memory warning.

`tools/artifact-release.js refresh` consumed both receipts and derived exactly two blockers: the current inputs have no immutable source revision, and no cold-checkout receipt can identify that revision.  The kernel scope audit passed for the proof tree and its two local imports, and `node test/run_all.js` passed 791 accepted cases, 45 expected rejections, 14 expected traps, 340 standard-Lean comparisons, 62 IR comparisons, and 56 fuzz cases.  The clean-checkout run requires a committed source revision containing every tracked cache and proof input.

## 2026-08-02: Verification Command Boundaries

Repository verification commands define the reusable approval boundaries.  Direct Lean diagnostics start with `tools/leanrun`, source-driven proof work starts with `tools/talos-artifact.js` or `tools/talos-proof.js`, exact-artifact proofs start with `tools/artifact-proof.js`, official-corpus checks start with `tools/artifact-conformance.js`, and release checks start with `tools/artifact-release.js`.  An approval for one of those command prefixes covers its supported subcommands and future configured cases.

Official execution files, invalid modules, assertion lines, and expected classifications belong in `proofs/talos/conformance.json`, which `tools/artifact-conformance.js check` validates and consumes.  Direct shell expansion of corpus filenames bypasses that boundary and causes the approval system to record an expanded one-off command.  Cold-checkout setup and both release gates remain inside `tools/artifact-release.js check-cold <revision>`, so the later network and temporary-checkout operation needs one repository-tool approval rather than approvals for its internal Git, download, Lake, proof, and conformance commands.

## 2026-08-02: Schema-Three Artifact and Release Evidence

All twenty artifact manifests now use schema three and name the embedded bytes, decoded raw cache, execution cache, closed artifact theorem, and concrete behavioral theorems.  Each generated `artifact_module_eq_cache` theorem contains decode and validation witnesses, a `CoreValid` proof, and equality between the validated translation and the execution cache.  The aggregate artifact gate checked the exact declaration types and printed the axiom dependencies for every manifest theorem in addition to rebuilding all twenty behavioral specifications.

The declaration audit rejects `sorryAx` and accepts only `propext`, `Classical.choice`, `Quot.sound`, `Lean.ofReduceBool`, and theorem-local certificate axioms generated by `native_decide` or `bv_decide`.  The verifier-source digest covers seventeen named normative files, while the canonical release-input digest also covers toolchain pins, registries, manifests, binaries, conformance configuration, and proof-workspace inputs.  The successful aggregate receipt records twenty artifacts and release-input SHA-256 `5a9545ec3788a95a0cd3a6c73a419748ff1c4fed46d49821d85c880fbd05abaa`.

Both Lean workspaces pin 4.31.0 at commit `68218e876d2a38b1985b8590fff244a83c321783`, and that kernel accepts the archived reproduction at source `e7c533e752bf4a4cc9e0170cc0972824c46ef755:proofs/talos/lean/Examples/KernelUnsoundness.lean`.  The owner accepts this known defect for the artifact release after `tools/artifact-release.js audit-kernel-scope` found no literal `addDecl` or `inductDecl` references in `proofs/talos/lean/Project` or its two local imports, `LeanExe/Examples/AsciiDigits.lean` and `LeanExe/Examples/TalosAssocList.lean`.  This lexical audit does not cover dependencies, aliases, compiled declarations, elaborator internals, other environment-mutation APIs, or the kernel defect itself, and the release record preserves that limitation.

`tools/artifact-release.js refresh` reconstructs the package records and consumes only warm receipts whose canonical input digest matches the current repository.  The current draft has exactly two derived blockers: no immutable source revision records the implementation, and no cold-checkout receipt can identify that revision.  `check-cold <revision>` compares canonical inputs before setup and after both gates, verifies the exact Lean and dependency revisions, rejects tracked mutations, and writes a receipt only after success.

Checks run:

- [x] `tools/artifact-proof.js check-all` passed twenty schema-three packages and wrote the matching artifact receipt.
- [x] `tools/artifact-conformance.js check` passed with the exact imported-memory warning and wrote the matching conformance receipt.
- [x] `tools/artifact-release.js audit-kernel-scope` passed for the proof tree, its two local imports, and both forbidden identifiers.
- [x] `tools/artifact-release.js refresh` consumed both warm receipts and reported two blockers.
- [x] `node test/artifact_identity.js` checked the verifier membership and canonical digest vectors.
- [x] `node test/artifact_migrate.js` checked transactional migration and frozen-file identity.
- [x] `node test/artifact_release.js` checked identities, receipts, pins, results, and blocker derivation.
- [x] `node test/run_all.js` passed 791 accepted cases, 45 expected rejections, 14 expected traps, 340 standard-Lean comparisons, 62 IR comparisons, and 56 fuzz cases after the JavaScript execution guard was corrected to distinguish identifiers from strings and comments.

## 2026-08-02: Official Corpus Conformance Gate

`tools/artifact-conformance.js check` now verifies and executes a pinned official WebAssembly corpus slice.  The configuration records CodeLib revision `bb3277e21c9786e3133d5c1601e34ebdc0bea4df`, testsuite revision `9233a0a8d5920a8d32358ee915a3662ff3385029`, Wasmtime 44.0.0, and the `function-references=y` option.  The driver also checks `wasm-tools` 1.251.0, stages each exact file in a one-file temporary corpus, and runs every Lean-based build or Talos execution serially through `tools/leanrun`.

The configuration also pins fifteen official invalid modules by file, assertion kind, source line, expected classification stage, and exact error constructor.  The driver extracts those commands with `wasm-tools json-from-wast`, strips encoder-added custom sections from text-origin `assert_invalid` modules, preserves raw `assert_malformed` binaries, and classifies all staged modules in one resource-limited Lean process.  All fifteen matched, covering malformed headers and sections, integer overflow, invalid alignment and memory limits, stack underflow, and stack-height mismatches.

The selected slice contains twenty-five files covering the accepted integer, control, call, local, memory, conversion, function, label, and expression forms.  Talos reported 3,853 passes, six known assertion failures, 627 skips, and no cascades, decoder errors, interpreter errors, or fuel exhaustion.  Wasmtime passed all twenty-five files, and every Talos failure occurred in `memory_grow.wast`.

The failing assertions import a memory exported with maximum five pages through a declaration that permits six pages.  Talos copies the memory value into the importer and computes `memory.grow` capacity from the import declaration, so the imported memory grows from five to six pages when the official semantics require `-1` and a retained size of five.  The accepted artifact-verification profile contains no imports, so the gate treats the exact six-row fingerprint as an upstream warning, removes the warning at zero failures, and rejects every changed or additional failure.

Building the pinned testsuite from a cold dependency tree required dividing the import closure before the executable target.  `Mathlib.Tactic.NormNum.LegendreSymbol`, `Mathlib.Tactic`, `Interpreter.Wasm`, `Interpreter.Testsuite.Exec`, and `Interpreter.Testsuite` built in sequence before `testsuite`, whose final build completed 5,960 jobs.  The executable's large closure comes from `Interpreter.Testsuite.Exec` importing the `Interpreter.Wasm` umbrella, which includes weakest-precondition modules and `Mathlib.Tactic`.

The asynchronous process helper now drains captured stdout and stderr and includes both streams in failure messages.  Unit tests cover output capture, async error detail, exact file selection, totals parsing, detailed failure parsing, known-issue classification, Lean command routing, and signal forwarding.  Wasmtime executions run under a five-minute timeout, while Talos executions retain the ten-minute `tools/leanrun` limit.

Checks run:

- [x] `node --check tools/artifact-conformance.js`
- [x] `node --check tools/run-process.js`
- [x] `node --check test/artifact_conformance.js`
- [x] `node --check test/run_process.js`
- [x] `node test/artifact_conformance.js` returned `checked conformance parsing, known issues, official validator cases, and file selection`.
- [x] `node test/run_process.js` returned `checked sync and async process errors, output capture, Lean command routing, and signal forwarding`.
- [x] `tools/artifact-conformance.js check` classified all fifteen official invalid modules, reported all twenty-five Talos and Wasmtime results, and passed with one warning for the exact six imported-memory failures.

## 2026-08-02: Complete Aggregate Artifact Gate

`tools/artifact-proof.js check-all` passed all twenty registered artifacts under the standard `tools/leanrun` resource policy.  The command checked each frozen file's SHA-256, length, package identity, and equality with its embedded Lean byte value, then built every decode, validation, exact translation, artifact-correctness, and behavioral target.  The final generated declaration module checked every theorem name recorded by the manifests and reported `Aggregate artifact proof passed: 20 artifacts`.

The LEB128 proof reached this result after division into reusable positive and negative iteration, completion, allocation, and prefix lemmas.  `Project.LebU32.NegFreshAlloc` states the exact fresh-allocation header writes and allocation prelude with an arbitrary postcondition, while `NegAfterFree`, `NegPrefix`, `NegIter`, and `Main` compose those results at the generated instruction boundaries.  The aggregate then passed every CLOB target; the largest measured modules were `Project.ClobCancel.Spec` at 1,092 seconds, `Project.ClobMatchFuel.FindBest` at 696 seconds, and `Project.ClobMatchFuel.Helpers` at 384 seconds.

The artifact driver now uses the shared asynchronous process helper instead of blocking in `spawnSync`.  The helper starts each child in a process group, forwards `SIGINT` and `SIGTERM`, waits for the child to close, and prevents an interrupted Node driver from leaving its runner, Lake process, or Lean child behind.  The focused process test confirmed that `SIGTERM` reaches a grandchild, and `tools/artifact-proof.js check-artifacts` then passed all twenty exact artifact targets through the revised command path.

Checks run:

- [x] `tools/artifact-proof.js check-all` returned `Aggregate artifact proof passed: 20 artifacts`.
- [x] `node --check tools/run-process.js`
- [x] `node --check tools/artifact-proof.js`
- [x] `node --check test/run_process.js`
- [x] `node test/run_process.js` returned `checked sync and async process errors, output capture, Lean command routing, and signal forwarding`.
- [x] `tools/artifact-proof.js check-artifacts` returned `Aggregate artifact theorem pass completed: 20 artifacts` through the signal-aware driver.

## 2026-08-01: Binary Decoder Soundness

The binary proof now defines exact cursor consumption and proves soundness for fixed bytes, bounded parsers, vectors, names, unsigned and signed LEB128, every accepted instruction, expressions, code bodies, sections, and complete modules.  The independent grammar now requires strict section ordering and uniqueness through increasing section ranks.  The theorem `Wasm.Binary.Proof.decode_sound` proves that every successful `decode` result satisfies `Grammar.Encodes` for the complete input `ByteArray`.

The section-loop proof tracks bytes consumed by each section, agreement between assigned fields and the final module, and preservation of empty fields for absent sections.  The decoder uses named opcode classification and a named section-step parser so the execution proof composes at stable parser boundaries.  `tools/leanrun --timeout 300 lake -d proofs/talos/lean env lean proofs/talos/lean/Project/Artifact/Binary/Proof/Decode.lean` completed successfully under the shared cgroup and machine-wide Lean lock.

## 2026-08-01: Artifact Decoder, Validator, and Talos Translation

The artifact-verification implementation now has a repository-owned raw WebAssembly syntax, bounded byte cursor, unsigned and signed LEB128 parsers, UTF-8 name parser, structured instruction decoder, restricted module decoder, executable validator, and Talos translation.  The accepted profile covers the type, function, memory, global, export, and code sections and every opcode emitted by the current compiler artifacts.  `docs/artifact-format.md` records the profile, trusted base, raw representation, package layout, and manifest fields against the WebAssembly Core 3.0 binary and validation specifications.

All twenty current `.generated` binaries decode, validate, and translate in one Lean process under `tools/leanrun`.  A separate comparison imports the twenty WAT-derived Talos caches and matches every translated module on functions, types, function exports, memory, and globals.  Focused primitive, corruption, and invalid-module tests cover LEB width boundaries, permitted overlong forms, truncation, trailing bytes, invalid UTF-8, section errors, type-index errors, memory limits, stack underflow, branch depth, local indices, immutable globals, alignment, and duplicate exports.

`Project.Artifact.Binary.Grammar` defines an independent declarative grammar over byte lists, including non-canonical LEB encodings permitted by the specification.  Decoder soundness against that grammar and validator soundness against an independent `CoreValid` relation remain unproved, so the current executable results do not constitute artifact-level verification.  The permanent decoder location in a pinned Talos fork and the Lean kernel build also remain unresolved design gates.

The GCD pilot embeds all 1,249 artifact bytes and records SHA-256 `51801200954786e42d28caf3ba8806d613ab31ec4abe9b5d4b672e28d953b3ae`.  Its generated raw cache builds separately, and a generic evidence lemma turns a successful computed `verifiedModule?` certificate into explicit decode and validation witnesses.  The GCD artifact target builds through this boundary, while its Boolean raw-cache comparison remains a test until a proved equality procedure or grammar-unambiguity theorem connects that result to propositional equality.

Whole-module kernel reduction does not provide a usable cache-equality boundary.  A direct theorem combining decode, validation, translation, and equality with `Project.Gcd.Program.module` reached a 300-second no-diagnostic timeout, a function-level theorem that still unfolded the whole decoder reached a 180-second no-diagnostic timeout, and isolated `decode artifactBytes = .ok cachedRaw` reached a 300-second no-diagnostic timeout.  The next proof work must use compositional parser soundness, grammar unambiguity, and small generated certificates rather than rerunning any of those unchanged terms.

The PairFree proof division produced a stable `Project.PairFree.BuildCore` target that built in 19 seconds.  `Project.PairFree.BuildTail` first produced a final-store bound diagnostic after 276 seconds, then reached a 360-second no-diagnostic timeout after that bound was added.  A smaller allocation-prefix probe also reached a 300-second no-diagnostic timeout, so the unchanged proof slices must remain unrun until another reusable lemma or module boundary reduces elaboration.

Checks run:

- [x] `tools/leanrun --timeout 180 lake --dir proofs/talos/lean --no-ansi build Project.Artifact.Binary.PrimitivesTests`
- [x] `tools/leanrun --timeout 180 lake --dir proofs/talos/lean --no-ansi build Project.Artifact.Binary.DecodeTests`
- [x] `tools/leanrun --timeout 180 lake --dir proofs/talos/lean --no-ansi build Project.Artifact.Binary.ValidateTests`
- [x] One `ValidateFile` run decoded and validated all twenty current artifacts.
- [x] One `TranslateFile` run decoded, validated, and translated all twenty current artifacts.
- [x] One `CompareCaches` run returned `matched` for all twenty current WAT-derived Talos caches.
- [x] `tools/leanrun --timeout 240 lake --dir proofs/talos/lean --no-ansi build Project.Artifact.Binary.Grammar`
- [x] `tools/leanrun --timeout 120 lake --dir proofs/talos/lean --no-ansi build Project.Artifact.Binary.Evidence`
- [x] `tools/leanrun --timeout 120 lake --dir proofs/talos/lean --no-ansi build Project.Gcd.Artifact`

## 2026-06-19: Talos Proof for Generated GCD WASM

`LeanExe.Examples.TalosGcd.gcd` is a small Euclidean GCD program written in the supported Lean subset.  The LeanExe compiler emits the WASM artifact stored at `proofs/talos/rust/build/gcd/program.wasm`; `wasm-tools print` produces the WAT that Talos decodes into `Project.Gcd.Program`.  The proof in `proofs/talos/lean/Project/Gcd/Spec.lean` states that exported function `0` terminates for all `UInt64` inputs and returns `UInt64.ofNat (Nat.gcd a.toNat b.toNat)`.

The proof follows the generated WASM, including the compiler’s Boolean-normalization blocks, rather than a hand-written WAT model.  Its loop invariant names the generated local frame, treats WASM locals `4` and `5` as the Euclidean state, leaves scratch locals unconstrained, and uses `y.toNat` as the decreasing measure.  The generated module includes LeanExe runtime exports, but the `gcd` export itself does not touch memory or call runtime functions, so the spec is store-parametric.

`tools/check-talos-gcd.sh` is the integrity check for this proof slice.  It rebuilds the Lean source with `lean-wasm`, emits a fresh WASM file, prints fresh WAT with `wasm-tools`, compares both files against the Talos proof inputs, and then rebuilds the Talos Lean proof project.  The script accepts `WASM_TOOLS` or finds `$HOME/.cargo/bin/wasm-tools`, because `cargo install` does not guarantee the binary is on the noninteractive shell path.

Checks run:

- [x] `bash tools/check-talos-gcd.sh` rebuilt `LeanExe.Examples.TalosGcd`, compared regenerated WASM and WAT against `proofs/talos/rust/build/gcd/`, and built the Talos proof project.
- [x] `build/tools/wasmtime/current/wasmtime --invoke gcd proofs/talos/rust/build/gcd/program.wasm 48 18` returned `6`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke gcd proofs/talos/rust/build/gcd/program.wasm 270 192` returned `6`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke gcd proofs/talos/rust/build/gcd/program.wasm 17 0` returned `17`.

## 2026-06-16: Helper Result Owner Aliases

The orderbook WASM harness exposed a release-analysis bug in functions that return heap-bearing structures assembled from helper results.  The reduced case was a depth state with `bids` and `asks` arrays: the recursive helper returned one accumulator array unchanged, while the caller copied the helper result into a `DepthResult` and then released the original empty array local.  Rendering the returned result then read a freed empty array; empty stdin produced corrupt depth output, and non-empty stdin trapped in Wasmtime.

Release analysis now expands returned owner slots through local lets and helper calls before deciding which non-recursive owned temporaries can be released.  A helper call contributes its argument slots to that expansion only when the helper has heap parameters and at least one heap result owner that the existing fresh-result summary does not prove fresh.  This keeps the existing release behavior for helpers that return newly allocated arrays or byte arrays, while preserving argument-owned roots returned through accumulator helpers.

The new `depthAliasRun` WASI example in `LeanExe.Examples.Correctness` keeps the failing shape without importing the orderbook module.  It selects a bid-only or ask-only book from stdin, computes old-style depth through a two-array state, and renders both sides into `ByteArray`.  Before the fix, empty stdin emitted the corrupt sequence beginning `0 1 12 6 48 5501223100278326855`, and stdin `x` trapped at `wasm unreachable`; after the fix, the outputs are `0 1 12 6 0\n` and `0 0 1 100 6\n`.

Checks run:

- [x] `lake build LeanExe.Extract.Values`
- [x] `lake build lean-wasm`
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin-except --max-input-bytes 16 --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.depthAliasRun --out .lake/build/wasi-programs/depthAliasRun.final.wasm`
- [x] `timeout 5s build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/depthAliasRun.final.wasm < /dev/null` returned `0 1 12 6 0`.
- [x] `printf x | timeout 5s build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/depthAliasRun.final.wasm` returned `0 0 1 100 6`.
- [x] `node test/wasi_program.js` returned `checked 35 WASI program cases, 2 traps, and 7 rejections`.
- [x] `node test/refcount.js` returned `checked 38 refcount cases`.
- [x] `node test/ownership_report.js` returned `checked 8 ownership report cases`.
- [x] `node test/core_correctness.js` returned `checked 784 accepted, 34 rejected, and 13 trapped cases`.
- [x] In `orderbook-wasm`, `lake env ../leanexe/.lake/build/bin/lean-wasm compile-wasi-stdin-except --max-input-bytes 16 --module PmobOrderBook.LeanExeDepthRenderRepro --entry PmobOrderBook.LeanExeDepthRenderRepro.run --out .lake/build/repro-depth-old-state.fixed.wasm`, followed by empty stdin and stdin `x` Wasmtime runs, returned `0 1 12 6 0` and `0 0 1 100 6`.
- [x] In `orderbook-wasm`, `lake env ../leanexe/.lake/build/bin/lean-wasm ownership-report --module PmobOrderBook.LeanExeDepthRenderRepro --entry PmobOrderBook.LeanExeDepthRenderRepro.run` showed `PmobOrderBook.LeanExeDepthRenderRepro.oldDepth` with `compiler statement releases: none`.
- [x] In `orderbook-wasm`, `lake env ../leanexe/.lake/build/bin/lean-wasm compile-wasi-stdin-except --max-input-bytes 4096 --module PmobOrderBook.RawCommand --entry PmobOrderBook.RawCommand.run --out .lake/build/pmob-orderbook-raw.wasm`
- [x] In `orderbook-wasm`, `lake env lean PmobOrderBook/KernelTest.lean`
- [x] In `orderbook-wasm`, `lake env lean PmobOrderBook/RawCommandTest.lean`
- [x] In `orderbook-wasm`, `lake env lean PmobOrderBook/LeanExeDepthRenderReproTest.lean`
- [x] In `orderbook-wasm`, `go test -count=1 ./harness` returned `ok  	leanclob/orderbookwasm/harness	5.232s`.

## 2026-06-16: Type-Class Specialization Through List Helpers

Type-class evidence specialization now feeds the expression-level structural-recursion discovery pass.  When a same-root helper call has static class evidence and concrete supported runtime arguments, the discovery pass inline-specializes the helper body, normalizes class evidence, and collects any structural-recursion helpers exposed by the specialized body.  This lets generic class-constrained helpers compile when their specialized bodies call `List.foldl` or `List.find?` over supported element layouts.

The new correctness examples use `TypeclassScore` over `List (Option UInt64)`.  `typeclassScoreListFoldlDemo` folds scores through `List.foldl`, and `typeclassScoreListFindDemo` searches with `List.find?` before scoring the returned value.  Direct `List.any` remains covered by existing closed-predicate tests, but the generic class-constrained `List.any` shape still needs a predicate-extraction improvement.

Checks run:

- [x] `lake build LeanExe.Extract.Core LeanExe.Examples.Correctness lean-wasm`
- [x] `node --check tools/compare-standard.js`
- [x] `node --check test/core_correctness.js`
- [x] `node --check test/report_classification.js`
- [x] `node test/run_all.js` returned `checked 114 report classification cases`, `checked 8 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 784 accepted, 34 rejected, and 13 trapped cases`, `checked 38 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 298 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-28: Type-Class Boundary Hardening

Type-class diagnostics now distinguish public runtime evidence from internal evidence-bearing helpers.  Public entries with unresolved class evidence or explicit dictionary parameters reject with `runtime class evidence is not supported`, while the report command describes internal class methods, instances, and class constructors as static-specialization requirements.  The report remains entry-aware, so accepted concrete wrappers can mention class declarations in their dependency graph without marking the whole reachable graph as rejected.

Evidence normalization now runs at class-method application sites that reach extraction after specialization, which lets source-defined class methods compile inside additional direct-lambda array callbacks.  The correctness examples now compare `TypeclassScore` methods inside `Array.any` and `Array.find?`, in addition to the earlier `Array.foldl` case.  The BEq path keeps custom lambda instances on the normalization path, but it preserves the existing structural equality lowering for evidence that is structurally derived or built from `instBEqOfDecidableEq`, including `Option.instBEq` and `Array.instBEq`.

This pass also filled direct fixed-width primitive gaps exposed by the stricter evidence handling.  Direct `UInt64`, `UInt32`, and `UInt8` comparison methods lower as conditions, direct `UInt64`, `UInt32`, and `UInt8` complement methods lower without relying on class projection unfolding, and direct `UInt8.land`, `UInt8.lor`, and `UInt8.xor` now share the existing fixed-width bitwise lowering.  Numeric class projections already handled by primitive extraction stay on that explicit path instead of being unfolded through library instance bodies.

Checks run:

- [x] `lake build LeanExe.Extract.Core lean-wasm`
- [x] `lake build LeanExe.Extract.Report lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness lean-wasm`
- [x] `node --check tools/compare-standard.js`
- [x] `node --check test/core_correctness.js`
- [x] `node --check test/report_classification.js`
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry typeclassScoreArrayAnyDemo --result-slots '#[__leanexeValue]'` returned `matched pure LeanExe.Examples.Correctness.typeclassScoreArrayAnyDemo`.
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry typeclassScoreArrayFindDemo --result-slots '#[__leanexeValue]'` returned `matched pure LeanExe.Examples.Correctness.typeclassScoreArrayFindDemo`.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.rejectTypeclassEntry --out .lake/build/typeclass-reject-entry.wasm` rejected with `runtime class evidence is not supported: LeanExe.Examples.Correctness.rejectTypeclassEntry`.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.rejectTypeclassRuntimeDictionaryParam --out .lake/build/typeclass-reject-dict.wasm` rejected with `runtime class evidence is not supported: LeanExe.Examples.Correctness.rejectTypeclassRuntimeDictionaryParam`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 296 standard Lean comparison cases`.
- [x] `node test/core_correctness.js` returned `checked 782 accepted, 34 rejected, and 13 trapped cases`.
- [x] `node test/bytearray_alloc.js` returned `checked 70 bytearray allocation cases`.
- [x] `node test/report_classification.js` returned `checked 113 report classification cases`.
- [x] `node test/run_all.js` returned `checked 113 report classification cases`, `checked 8 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 782 accepted, 34 rejected, and 13 trapped cases`, `checked 38 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 296 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-28: Static Type-Class Evidence

LeanExe now treats class evidence as a static specialization input for inline-specialized helpers.  The classifier reads Lean's imported class-extension entries directly instead of importing modules with `loadExts := true`, which preserves access to source-defined classes without requiring imported initializer execution in the `lean-wasm` executable.  Specialized helper bodies run through bounded evidence normalization that beta-reduces, unfolds class evidence applications, unfolds class projection functions, and reduces projections from class constructors before ordinary extraction.

The correctness examples cover `BEq`, `Inhabited`, and a source-defined `TypeclassScore` class.  The custom `BEq` example is intentionally nonstructural, so it catches the unsound path where generic `==` would ignore the selected instance and lower to structural equality.  The `TypeclassScore` examples cover scalar and structure instances, a dependent `Option` instance, and a class method used inside an `Array.foldl` direct lambda.  Runtime dictionaries, exported unresolved class constraints, dynamic dispatch, and unsupported method result types remain outside the accepted subset.

The implementation also adds direct lowering for `UInt64`, `UInt32`, and `UInt8` arithmetic primitives exposed after method inlining, plus proof-erased lowering for `UInt64.ofNatLT`, `UInt32.ofNatLT`, and `UInt8.ofNatLT`.  Those forms are not type-class-specific; they are ordinary checked Lean fixed-width integer operations that became visible once evidence normalization exposed method bodies.  The `ofNatLT` match uses plain `Name` values because quoting the external declaration in the compiled extractor made the native `lean-wasm` executable look for a nonexistent runtime implementation of that checked constructor.

Checks run:

- [x] `lake build LeanExe.Extract.Types LeanExe.Extract.Core lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node --check tools/compare-standard.js`
- [x] `node --check test/core_correctness.js`
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry typeclassSameUInt64 --result-slots '#[__leanexeValue]'` returned `matched pure LeanExe.Examples.Correctness.typeclassSameUInt64`.
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry typeclassSameCustomBEq --result-slots '#[__leanexeValue]'` returned `matched pure LeanExe.Examples.Correctness.typeclassSameCustomBEq`.
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry typeclassDefaultUInt64 --result-slots '#[__leanexeValue]'` returned `matched pure LeanExe.Examples.Correctness.typeclassDefaultUInt64`.
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry typeclassDefaultPoint --result-slots '#[__leanexeValue]'` returned `matched pure LeanExe.Examples.Correctness.typeclassDefaultPoint`.
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry typeclassScoreUInt64 --result-slots '#[__leanexeValue]'` returned `matched pure LeanExe.Examples.Correctness.typeclassScoreUInt64`.
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry typeclassScorePoint --result-slots '#[__leanexeValue]'` returned `matched pure LeanExe.Examples.Correctness.typeclassScorePoint`.
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry typeclassScoreOptionUInt64 --result-slots '#[__leanexeValue]'` returned `matched pure LeanExe.Examples.Correctness.typeclassScoreOptionUInt64`.
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry typeclassScoreArrayTotalDemo --result-slots '#[__leanexeValue]'` returned `matched pure LeanExe.Examples.Correctness.typeclassScoreArrayTotalDemo`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 294 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 8 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 780 accepted, 32 rejected, and 13 trapped cases`, `checked 38 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 294 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-28: Type-Class Implementation Plan

`typeclasses.md` records the literature context and implementation plan for type-class support.  The design conclusion is static evidence specialization: Lean should perform instance search, and LeanExe should specialize the elaborated evidence terms until class methods become ordinary first-order code or reject the program.  Runtime dictionaries, witness tables, indirect calls, and a public ABI for class evidence remain outside the first implementation slice.

The plan is staged around evidence classification, bounded evidence normalization, specialization keys for static arguments, method lowering after specialization, comparison tests against standard Lean, and documentation updates.  The first accepted examples should cover `BEq`, `Inhabited`, and a source-defined class with dependent instances.  Rejection tests should cover exported unresolved class constraints, escaping dictionary values, unsupported method result types, and evidence normalization that fails to reach first-order code.

## 2026-05-22: Tagged List Fold Accumulators

Specialized inline calls now beta-reduce instantiated dependent domains and result types before classifying them.  This fixes generated match helpers whose declared result is `motive acc item`: after substituting a direct motive lambda, the result is an ordinary supported value type, but the previous classifier inspected the unreduced application and rejected the helper as an unsupported function type.

The standard comparison corpus now accepts closed `List.foldl` examples whose accumulators are heap-bearing tagged values.  The new cases cover `Option ByteArray` and `Except ByteArray ByteArray` accumulators over list elements that also contain heap-bearing tags, and both cases compare generated WASM under Wasmtime with the standard Lean toolchain.

Checks run:

- [x] `lake build LeanExe.Extract.Core LeanExe.Examples.Correctness lean-wasm`
- [x] `node --check tools/compare-standard.js`
- [x] `node --check test/core_correctness.js`
- [x] `node tools/compare-standard.js --mode pure-bytes --module LeanExe.Examples.Correctness --entry optionByteArrayListFoldlTaggedAccumulatorValue --serializer 'LeanExe.Examples.Correctness.optionByteArrayBytes __leanexeValue'` returned `matched pure-bytes LeanExe.Examples.Correctness.optionByteArrayListFoldlTaggedAccumulatorValue`.
- [x] `node tools/compare-standard.js --mode pure-bytes --module LeanExe.Examples.Correctness --entry exceptByteArrayUInt64ListFoldlTaggedAccumulatorValue --serializer 'LeanExe.Examples.Correctness.exceptByteArrayByteArrayBytes __leanexeValue'` returned `matched pure-bytes LeanExe.Examples.Correctness.exceptByteArrayUInt64ListFoldlTaggedAccumulatorValue`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 286 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 8 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 772 accepted, 32 rejected, and 13 trapped cases`, `checked 38 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 286 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Heap-Bearing List Fold Comparisons

The standard comparison corpus now covers heap-bearing `List.foldl` and `List.foldr` results over `List (Option ByteArray)` and `List (Except ByteArray UInt64)`.  The accepted cases return `ByteArray` values directly and return a `ByteOutputState` structure that carries a byte-array accumulator.  The corpus also records direct `List.concat` as accepted after verifying the generated WASM against standard Lean with the appended element demanded by a structural sum.

The new rejection cases marked the then-current boundary around closed structural folds.  Local callback values, function-valued accumulators, nested closed folds, and a tagged `Option ByteArray` accumulator that lowered through an unsupported generated matcher were outside the accepted subset at this checkpoint.  The 2026-05-22 entry supersedes the tagged-accumulator part of that boundary.

Checks run:

- [x] `lake build LeanExe.Extract.Core LeanExe.Examples.Correctness lean-wasm`
- [x] `node --check tools/compare-standard.js`
- [x] `node --check test/core_correctness.js`
- [x] `node tools/compare-standard.js --self-test` returned `checked 284 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 8 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 772 accepted, 33 rejected, and 13 trapped cases`, `checked 38 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 284 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Heap-Tagged List Predicates

The standard comparison corpus now covers direct `List.any` and `List.all` over non-scalar element layouts.  The new cases exercise structures, source-defined tagged values, `ByteArray`, `Option UInt64`, `Option ByteArray`, and `Except ByteArray UInt64`, comparing standard Lean execution with generated WASM under Wasmtime.

The recursive-family specialization also now has heap-bearing tagged list-result cases.  `List (Option ByteArray)` and `List (Except ByteArray UInt64)` are tested through `List.map`, `List.filter`, `List.find?`, and append after reverse with source-level byte serializers.  One serializer alias had to be eta-expanded because the extractor accepts ordinary function bodies at that boundary, not a bare definition alias.

Checks run:

- [x] `lake build LeanExe.Extract.Core LeanExe.Examples.Correctness lean-wasm`
- [x] `node --check tools/compare-standard.js`
- [x] `node --check test/core_correctness.js`
- [x] `node tools/compare-standard.js --self-test` returned `checked 277 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 8 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 771 accepted, 29 rejected, and 13 trapped cases`, `checked 38 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 277 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Non-Scalar List Comparisons

The standard comparison corpus now covers monomorphic `List` values whose elements are structures, source-defined tagged values, byte arrays, and nested `Option` values.  The new fixtures exercise `List.map`, `List.filter`, `List.find?`, append after reverse, `List.foldl`, and `List.foldr`, comparing standard Lean execution with generated WASM under Wasmtime through byte serializers or scalar slots.  This extends the tested recursive-family specialization beyond `List UInt64` without adding a list-specific compiler path.

The first `List (Option UInt64).find?` case exposed a missing condition-extraction branch for generated `Option` matchers.  Value extraction already accepted that matcher form, but condition extraction skipped from generated `Except` matches to `Nat` matches.  The extractor now routes generated `Option` matchers used as conditions through the ordinary value extractor before converting the scalar result to a condition.

Checks run:

- [x] `lake build LeanExe.Extract.Core LeanExe.Examples.Correctness lean-wasm`
- [x] `node --check tools/compare-standard.js`
- [x] `node --check test/core_correctness.js`
- [x] `node tools/compare-standard.js --mode pure-bytes --module LeanExe.Examples.Correctness --entry optionUInt64ListFindValue --serializer 'LeanExe.Examples.Correctness.optionOptionUInt64Bytes __leanexeValue'` returned `matched pure-bytes LeanExe.Examples.Correctness.optionUInt64ListFindValue`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 257 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 8 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 771 accepted, 29 rejected, and 13 trapped cases`, `checked 38 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 257 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Recursive Flow Comparisons

The standard comparison corpus now covers recursive `U64Binary` values flowing through ordinary first-order program shapes.  The new fixtures compare `Option.map`, `Except.map`, `Except.bind`, branch-selected structures with recursive fields, source-defined tagged values with recursive payloads, arrays of recursive values, and `Id.run` loops carrying recursive, `Option` recursive, and `Except ByteArray` recursive state.  These tests compare standard Lean execution with generated WASM under Wasmtime through byte serializers, so the checked behavior is the source-level value rather than a hand-written numeric summary.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node --check tools/compare-standard.js`
- [x] `node --check test/core_correctness.js`
- [x] `node tools/compare-standard.js --self-test` returned `checked 233 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 8 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 771 accepted, 29 rejected, and 13 trapped cases`, `checked 38 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 233 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Conservative Recursive Cleanup

Recursive result cleanup now follows the project policy that leaks are acceptable and incorrect computation is not.  The result-materialization cleanup pass no longer emits compiler releases for ordinary recursive heap temporaries in scalar-result functions or heap-result functions.  It still releases nonrecursive owners such as `ByteArray` and `Array` when the existing local rules prove them fresh and absent from returned roots.

The aliasing corpus now includes source programs that share recursive children through constructor fields, return a subtree alias, duplicate recursive values in an array, duplicate recursive fields in a structure, and duplicate recursive payloads in a tagged value.  These cases compare the generated WASM under Wasmtime with standard Lean execution where possible.  The first version of the tests exposed unsafe compiler-inserted recursive releases in scalar-result functions, which now report no compiler statement releases in `ownership-report`.

Checks run:

- [x] `lake build LeanExe.Extract.Values LeanExe.Examples.Correctness lean-wasm`
- [x] `.lake/build/bin/lean-wasm ownership-report --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.u64BinarySharedChildScore` reported `compiler statement releases: none`.
- [x] `.lake/build/bin/lean-wasm ownership-report --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.u64BinaryReturnedSubtreeAliasScore` reported `compiler statement releases: none`.
- [x] `node --check test/core_correctness.js`
- [x] `node --check tools/compare-standard.js`
- [x] `node test/refcount.js` returned `checked 38 refcount cases`.
- [x] `node test/core_correctness.js` returned `checked 771 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 217 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 8 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 771 accepted, 29 rejected, and 13 trapped cases`, `checked 38 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 217 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Heap Owner Provenance

Owned-mask generation now tracks the local slot that first received an owned heap value.  When a later heap or array allocation consumes child slots, the compiler transfers ownership for only the first use of a source slot and retains later aliases.  Result materialization also refreshes owned masks after pruning local lets, so sequential source `let` bindings keep the ordered ownership context that extraction created.

`sharedRecursiveChildReleaseStats` covers the duplicate-reference case with a recursive binary tree.  The program constructs one leaf, stores that same leaf in both fields of a node, releases the node, and returns a packed counter value.  The expected `10302` means one retain during construction, three release calls during teardown, and two freed heap objects.

Checks run:

- [x] `lake build LeanExe.Extract.Values`
- [x] `lake build LeanExe.Examples.Correctness lean-wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.sharedRecursiveChildReleaseStats --out .lake/build/shared-recursive-child-release.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke sharedRecursiveChildReleaseStats .lake/build/shared-recursive-child-release.wasm` returned `10302`.
- [x] `node --check test/core_correctness.js`
- [x] `node --check test/refcount.js`
- [x] `node test/refcount.js` returned `checked 38 refcount cases`.
- [x] `node test/core_correctness.js` returned `checked 766 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 8 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 766 accepted, 29 rejected, and 13 trapped cases`, `checked 38 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 212 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Release Alias Propagation

A recursive value returned from a helper function trapped when source code released it with `LeanExe.Runtime.release`.  The helper result lived in local `2`, result materialization copied it into local `3`, and the source release consumed local `3`.  Release analysis propagated aliases inside a local-let prefix, but it did not propagate a release from the following body back into the prefix, so local `2` remained eligible for an automatic compiler release.

Release accounting now tracks release targets through `let` aliases and local-let prefixes using the set of slots released later in the expression or value.  A body release of an alias now marks the owner slot that produced the alias, while call-result ownership still treats returned slots as owned results rather than as ownership of the call arguments.  `recursiveScenarioHelperRuntimeReleaseStats` covers the helper-return case for leaf, balanced, and skewed recursive trees, and the ownership report asserts that the compiler emits no extra release for the helper result.

Checks run:

- [x] `lake build LeanExe.Extract.Values LeanExe.Examples.Correctness lean-wasm`
- [x] `.lake/build/bin/lean-wasm ownership-report --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.recursiveScenarioHelperRuntimeReleaseStats` reported `compiler statement releases: none`.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.recursiveScenarioHelperRuntimeReleaseStats --out .lake/build/recursive-helper-release.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke recursiveScenarioHelperRuntimeReleaseStats .lake/build/recursive-helper-release.wasm 0` returned `101`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke recursiveScenarioHelperRuntimeReleaseStats .lake/build/recursive-helper-release.wasm 1` returned `707`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke recursiveScenarioHelperRuntimeReleaseStats .lake/build/recursive-helper-release.wasm 2` returned `707`.
- [x] `node --check test/core_correctness.js`
- [x] `node --check test/refcount.js`
- [x] `node --check test/ownership_report.js`
- [x] `node test/ownership_report.js` returned `checked 8 ownership report cases`.
- [x] `node test/refcount.js` returned `checked 37 refcount cases`.
- [x] `node test/core_correctness.js` returned `checked 765 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 8 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 765 accepted, 29 rejected, and 13 trapped cases`, `checked 37 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 212 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Recursive Standard Comparisons

The standard comparison self-test now has parameterized recursive-value fixtures.  `leanListScenarioScore` compares empty, singleton, ordinary, and longer `List UInt64` inputs through scalar summaries, while `leanListScenarioReverseValue` and `leanListScenarioAppendMapValue` return recursive values that the wrapper serializes through the existing list renderer.  `u64BinaryScenarioScore` compares leaf, balanced, and skewed binary-tree shapes through scalar summaries, while `u64BinaryScenarioValue`, `u64BinaryScenarioMirrorValue`, `u64BinaryScenarioFindValue`, and `u64BinaryScenarioRequireByteErrorValue` compare returned recursive values, present and missing searches, and `Except ByteArray U64Binary` success and error paths.

Release-counter checks remain in the Wasmtime correctness and refcount suites because standard Lean defines `LeanExe.Runtime` counters as zero.  `recursiveScenarioRuntimeReleaseStats` now checks explicit source-level release of leaf, balanced, and skewed recursive trees, with the refcount suite asserting one released block for a leaf and seven released blocks for the nontrivial trees.  During exploratory testing, releasing a recursive value returned from a helper function trapped; that pattern needs a root-cause pass before it becomes a supported release-counter fixture.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness lean-wasm`
- [x] `node --check tools/compare-standard.js`
- [x] `node --check test/core_correctness.js`
- [x] `node --check test/refcount.js`
- [x] `node test/core_correctness.js` returned `checked 762 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/refcount.js` returned `checked 34 refcount cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 212 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 7 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 762 accepted, 29 rejected, and 13 trapped cases`, `checked 34 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 212 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Standard Comparison Edge Cases

The standard comparison self-test now covers more of the scalar and tagged-value perimeter against official Lean execution.  The added cases compare short-circuiting, fixed-width division by zero, UInt64 wrapping, Nat subtraction and division edge cases, fixed-width UInt8 and UInt32 wrapping, Option and Except public layouts, array reads, array filters, fixed-width array element operations, and selected foldr windows.  Pure comparison mode now normalizes successful Wasmtime `i64` CLI output back to unsigned `UInt64` text, because the harness slot type is `Array UInt64` while Wasmtime renders high-bit `i64` results as signed decimal.

The public ABI comparison slice now includes heap-bearing tagged argument values in addition to previous heap-bearing results.  It covers `Option (Array ByteArray)`, `Except ByteArray (Array ByteArray)`, `Array (Option ByteArray)`, `Array (Except ByteArray ByteArray)`, and `Option (Array (Option ByteArray))`, with both present and absent or error and ok constructor paths where those paths have different semantics.  These cases still compare standard Lean output with generated WASM executed under Wasmtime.

Checks run:

- [x] `node --check tools/compare-standard.js`
- [x] `node tools/compare-standard.js --self-test` returned `checked 189 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 7 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 751 accepted, 29 rejected, and 13 trapped cases`, `checked 31 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 189 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: More Standard Comparison Cases

The standard comparison self-test now includes repeated inputs for several programs rather than one representative call per entry.  The added cases cover pure scalar entries with different arguments, public nested-array and byte-array-array ABI arguments, byte-array stdin transforms on empty and nonempty input, JSON GCD success and error inputs, typed JSON object decoding success and schema-error inputs, JSON addition with reordered fields and overflow, Collatz JSON success and error inputs, and argv success and error behavior.  Each case still runs the official Lean program and compares it with the LeanExe-generated WASM under Wasmtime.

Checks run:

- [x] `node --check tools/compare-standard.js`
- [x] `node tools/compare-standard.js --self-test` returned `checked 126 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 7 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 751 accepted, 29 rejected, and 13 trapped cases`, `checked 31 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 126 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Array foldr

`Array.foldr` now lowers through the array multi-slot fold IR with an explicit traversal direction.  The reverse loop evaluates the array, `start`, `stop`, and initial accumulator once, clamps `start` to the array size, decrements before each load, and treats `stop` as the exclusive lower bound.  The direct-lambda body follows Lean's `α -> β -> β` binder order, while sharing the staged accumulator assignment and heap-accumulator release rule used by `Array.foldl`.

The correctness corpus covers the default scan, explicit windows, clamped starts, skipped empty bodies, structured accumulators, byte-array accumulators, and release counters.  Standard comparison checks both a scalar `foldr` result and a byte-array `foldr` result against the official Lean toolchain.  The specification, manual, README, and plan now describe `Array.foldr` as part of the supported fixed-width array surface, with attached-array erasure still limited to `foldl` and `foldlM`.

Checks run:

- [x] `lake build LeanExe.IR.Core LeanExe.Extract.Core LeanExe.Wasm.Binary LeanExe.Examples.Correctness lean-wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayFoldrDigits --out /tmp/arrayFoldrDigits.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke arrayFoldrDigits /tmp/arrayFoldrDigits.wasm` returned `321`.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayFoldrByteArrayAccumulatorReleaseStats --out /tmp/arrayFoldrByteArrayAccumulatorReleaseStats.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke arrayFoldrByteArrayAccumulatorReleaseStats /tmp/arrayFoldrByteArrayAccumulatorReleaseStats.wasm` returned `30202`.
- [x] `node --check test/core_correctness.js`
- [x] `node --check tools/compare-standard.js`
- [x] `node test/core_correctness.js` returned `checked 751 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 105 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 7 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 751 accepted, 29 rejected, and 13 trapped cases`, `checked 31 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 105 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Pure-ABI Parameter Comparisons

The standard comparison self-test now covers `pure-abi` library calls with heap-backed public parameters as well as heap-backed public results.  The added cases materialize nested scalar arrays, arrays of byte arrays, arrays of tagged values with byte-array payloads, and arrays of structures whose fields contain nested byte-array arrays through the Wasmtime C host script path.  A small `publicNestedArrayOpsReturn` correctness fixture gives `Array (Array UInt64)` a parameter-to-result case, matching the existing byte-array, tagged, and structured array examples.

The command-line path now has documented and tested `--abi-arg` coverage.  The standard Lean side receives an explicit `--standard-call`, while the generated WASM side receives the JSON-described ABI argument through the host runner and decodes the returned public ABI value from result slots plus targeted memory reads.

Checks run:

- [x] `node --check tools/compare-standard.js`
- [x] `node --check test/core_correctness.js`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node tools/compare-standard.js --self-test` returned `checked 103 standard Lean comparison cases`.
- [x] `node tools/compare-standard.js --mode pure-abi --module LeanExe.Examples.Correctness --entry publicByteArrayArrayOpsReturn --abi-layout '{"array":"ByteArray"}' --abi-arg '{"layout":{"array":"ByteArray"},"value":[[65],[66,67],[68,69,70]]}' --standard-call 'LeanExe.Examples.Correctness.publicByteArrayArrayOpsReturn #["A".toUTF8, "BC".toUTF8, "DEF".toUTF8]' --serializer '__leanexeJsonArray __leanexeValue __leanexeJsonByteArray'` returned `matched pure-abi LeanExe.Examples.Correctness.publicByteArrayArrayOpsReturn`.
- [x] `node test/core_correctness.js` returned `checked 744 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 7 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 744 accepted, 29 rejected, and 13 trapped cases`, `checked 31 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 103 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Standard Comparison for Public ABI Values

`tools/abi_layout.js` now owns the public ABI layout helpers that used to live inside `test/core_correctness.js`.  The shared code can materialize scalar, byte-array, array, structure, and tagged public arguments for the Wasmtime C host script runner, plan targeted memory reads for heap-backed results, decode those sparse memory reads back to JavaScript values, and compare nested ABI values structurally.

`tools/compare-standard.js` now has `pure-abi` mode for library exports whose public results contain heap-backed ABI values.  Standard Lean still computes the expected value, but the runner serializes that value to JSON through the caller's `--serializer`; the generated WASM is executed through the Wasmtime C host, and the result is decoded from ABI slots plus targeted memory ranges.  This adds standard Lean comparisons for public structure results with array fields, public `Array ByteArray`, public arrays of tagged values, and public arrays of structures with nested arrays.

Checks run:

- [x] `node --check tools/abi_layout.js`
- [x] `node --check test/core_correctness.js`
- [x] `node --check tools/compare-standard.js`
- [x] `node tools/compare-standard.js --mode pure-abi --module LeanExe.Examples.Correctness --entry publicByteArrayArrayReturn --abi-layout '{"array":"ByteArray"}' --serializer '__leanexeJsonArray __leanexeValue __leanexeJsonByteArray'` returned `matched pure-abi LeanExe.Examples.Correctness.publicByteArrayArrayReturn`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 98 standard Lean comparison cases`.
- [x] `node test/core_correctness.js` returned `checked 743 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 7 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 743 accepted, 29 rejected, and 13 trapped cases`, `checked 31 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 98 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Wasmtime Setup and Targeted Reads

`tools/download-wasmtime.sh` now downloads the Wasmtime CLI and matching C API archive into `build/tools/wasmtime`, using Wasmtime 44.0.0 and the detected Linux platform by default.  `tools/build-wasmtime-host.sh` derives the same version and platform, and still accepts `WASMTIME_C_API` for a custom C API package.  The repository-local Wasmtime setup is now reproducible from tracked tooling.

The C host script mode no longer dumps the full WASM memory for ABI assertions.  It keeps the Wasmtime instance alive after the call, supports `read-u64` and `read-memory` commands that can refer to result slots and earlier reads, and exits through an explicit `done` command.  `test/core_correctness.js` now plans the memory ranges required by each expected heap result and checks those ranges through a sparse memory reader.

Checks run:

- [x] `tools/download-wasmtime.sh`
- [x] `tools/build-wasmtime-host.sh`
- [x] `node --check test/wasmtime_host.js`
- [x] `node --check test/core_correctness.js`
- [x] `node test/core_correctness.js` returned `checked 743 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/no_js_wasm_execution.js` returned `checked JavaScript WASM execution guard`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 7 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 743 accepted, 29 rejected, and 13 trapped cases`, `checked 31 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 94 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Wasmtime Host Runner

The test suite now has a small C host runner built against the Wasmtime C API.  The runner instantiates a compiled library-mode module with Wasmtime, materializes `i64` and `ByteArray` arguments through the module's exported `alloc`, calls one exported function, and prints either an `i64`, flattened result slots, or returned bytes as hex.  This removes JavaScript WASM execution from the byte-array allocation tests, ASCII-string tests, JSON byte-transform tests, and validator fuzz test while preserving host-memory argument and result coverage for those cases.

The matching Wasmtime C API package for the existing CLI version is expected at `build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux-c-api`, or through `WASMTIME_C_API`.  `tools/build-wasmtime-host.sh` builds `build/tools/leanexe-wasmtime-host` from `tools/wasmtime-host.c`.  Node still orchestrates tests, but it no longer instantiates or executes WASM.

The runner now also owns the same-instance reference-count checks that used to require JavaScript's embedded engine.  Its dedicated commands cover release reuse, retained-pointer delayed reuse, the `free` alias, allocator growth, reset-sensitive temporary reuse for byte-array and array inputs, no-argument temporary reuse, and scalar calls with `Array UInt64` and `ByteArray` arguments.  A script mode lets `test/core_correctness.js` construct arbitrary public ABI inputs through symbolic `alloc`, byte writes, slot writes, and argument commands, then receive flattened result slots and targeted memory ranges for ABI assertions.  `test/no_js_wasm_execution.js` now fails the suite if test or tool JavaScript reintroduces direct WASM execution references.

Checks run:

- [x] `tools/build-wasmtime-host.sh`
- [x] `node --check test/wasmtime_host.js`
- [x] `node --check test/bytearray_alloc.js`
- [x] `node --check test/asciistring.js`
- [x] `node --check test/json_double.js`
- [x] `node --check test/fuzz_validate.js`
- [x] `node --check test/core_correctness.js`
- [x] `node --check test/no_js_wasm_execution.js`
- [x] `node test/bytearray_alloc.js` returned `checked 70 bytearray allocation cases`.
- [x] `node test/asciistring.js` returned `checked 23 asciistring cases`.
- [x] `node test/json_double.js` returned `checked 48 json program cases`.
- [x] `node test/fuzz_validate.js .lake/build/ascii-generic.wasm 10` returned `checked 16 cases`.
- [x] `node test/refcount.js` returned `checked 31 refcount cases`.
- [x] `node test/core_correctness.js` returned `checked 743 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/no_js_wasm_execution.js` returned `checked JavaScript WASM execution guard`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 7 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 743 accepted, 29 rejected, and 13 trapped cases`, `checked 31 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 94 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Heap-Bearing Array Ownership Tests

The correctness corpus now measures release behavior for arrays whose elements contain heap references through `Option ByteArray`, `PublicToken`, and `ByteArrayGroup`.  The refcount tests assert that source-level `Runtime.release` frees child values through the generic element layout, and the fold accumulator tests assert that array folds release replaced heap-bearing accumulators.  Public ABI rejection coverage now includes recursive values hidden inside `Option (Array U64List)`, a structure, and a tagged wrapper, so recursive public roots remain excluded even through otherwise supported containers.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node --check test/core_correctness.js`
- [x] `node --check test/refcount.js`
- [x] `node --check test/ownership_report.js`
- [x] `node test/ownership_report.js` returned `checked 7 ownership report cases`.
- [x] `node test/refcount.js` returned `checked 31 refcount cases`.
- [x] `node test/core_correctness.js` returned `checked 743 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 7 ownership report cases`, `checked 743 accepted, 29 rejected, and 13 trapped cases`, `checked 31 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 94 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Heap-Bearing Array Operations

The correctness corpus now exercises ordinary array operations over fixed-width heap-bearing element layouts.  The new entries cover `Array (Option ByteArray)`, `Array (Except ByteArray ByteArray)`, `Array PublicToken`, and `Array ByteArrayGroup`, where `ByteArrayGroup` contains an `Array ByteArray` field.  The exercised operations include public parameter materialization, public result decoding, `push`, append notation, `extract`, `setIfInBounds`, `insertIdxIfInBounds`, `eraseIdxIfInBounds`, `swapIfInBounds`, `reverse`, `map`, `filter`, `find?`, `findIdx?`, `any`, `all`, `foldlM`, and structural equality for arrays whose elements contain byte arrays or nested arrays.

No compiler change was required.  These tests verify that the fixed-width layout, child-owner masks, retained copied children, inactive tagged payload slots, and public ABI reader/writer helpers compose for the heap-bearing element layouts already accepted by the compiler.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness lean-wasm`
- [x] `node test/core_correctness.js` returned `checked 737 accepted, 25 rejected, and 13 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 112 report classification cases`.
- [x] `node test/run_all.js` returned `checked 112 report classification cases`, `checked 4 ownership report cases`, `checked 737 accepted, 25 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 94 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Public Tagged Heap Arrays

The public ABI coverage now includes heap-bearing arrays inside supported structures, nonrecursive tagged values, `Option`, and `Except`.  The correctness fixture covers public `Option (Array ByteArray)`, `Except ByteArray (Array ByteArray)`, arrays of `Option ByteArray`, arrays of `Except ByteArray ByteArray`, arrays of a source-defined `PublicToken` tag containing `ByteArray`, a public structure carrying `Array ByteArray`, and a public tagged result whose ok constructor carries `Array ByteArray`.  It also exercises `Array ByteArray` update, append, extract, insert, erase, swap, reverse, map, filter, find, any, all, and `foldlM` operations through public parameters and results.

The JS correctness harness now has composable ABI layout helpers for scalar slots, byte arrays, arrays, structures, and tagged values.  Tests can materialize nested public arguments and read nested public results through the same layout description, so future public ABI cases should not need one-off memory readers.  The old dedicated readers for public byte-array arrays, nested scalar arrays, and arrays of specific structures were removed from the active path.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness lean-wasm`
- [x] `node --check test/core_correctness.js`
- [x] `node test/core_correctness.js` returned `checked 722 accepted, 25 rejected, and 13 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 105 report classification cases`.
- [x] `node test/run_all.js` returned `checked 105 report classification cases`, `checked 4 ownership report cases`, `checked 722 accepted, 25 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 94 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-21: Public Heap-Bearing Arrays

The public array ABI now accepts fixed-width element layouts that contain heap-reference fields.  `Array ByteArray`, nested arrays such as `Array (Array UInt64)`, arrays of structures containing `ByteArray`, and arrays of structures containing array fields can appear as entry parameters and entry results.  The public element predicate is separate from the internal element predicate: it permits scalar values, `ByteArray`, nested arrays, structures, nonrecursive inductives, `Option`, and `Except` when all flattened fields meet the same rule, while recursive inductive values remain excluded from the public ABI.

The boundary representation uses the same slots as internal arrays.  `ByteArray` elements use owner, pointer, and length slots; nested arrays use owner and pointer slots.  Host-provided borrowed children use owner `0`, and compiler-owned result arrays retain the existing child-pointer mask behavior so `release` can reclaim owned byte arrays and nested arrays reached from an array result.

Checks run:

- [x] `lake build LeanExe.Extract.Types LeanExe.Extract.Values LeanExe.Examples.Correctness lean-wasm`
- [x] `node test/report_classification.js` returned `checked 97 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 703 accepted, 25 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 97 report classification cases`, `checked 4 ownership report cases`, `checked 703 accepted, 25 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 94 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Atomic Multi-Slot Fold Pruning

The liveness pass now treats a materialized multi-slot fold result as an atomic local assignment.  Before this change, a let-bound `Except UInt64 ByteArray` or `Option ByteOutputState` loop result could be pruned down to the tag and one scalar payload field when the later `match` ignored the byte-array payload.  That split one fold result into separate result-slot expressions, so the generated code ran the loop more than once and duplicated accumulator releases.

The pruning rule now keeps the complete `.slots` local let whenever `foldMultiSlotAssign?` recognizes the values as one fold assignment and any target slot remains live.  The ordinary scalar-slot pruning path still applies to unrelated `.slots` lets.  The counter examples now report the intended two loop-replacement releases and two frees: `exceptForByteArrayOutputReleaseStats` returns `10202`, and `optionForByteArrayStateReleaseStats` returns `30202`.

Checks run:

- [x] `lake build lean-wasm LeanExe.Examples.Correctness`
- [x] `node test/ownership_report.js` returned `checked 4 ownership report cases`.
- [x] `node test/core_correctness.js` returned `checked 695 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 4 ownership report cases`, `checked 695 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 94 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Ownership Report Command

`lean-wasm ownership-report --module M --entry E` now compiles the selected entry through the same two-pass extraction path as `compile`, then reports ownership data from the extracted IR.  The command lists each extracted function's result type, internal result owner offsets, helper-result fresh-owner offsets, returned owner expressions, compiler-emitted statement releases, fold accumulator release offsets, and explicit `LeanExe.Runtime.release` expressions.  `compileEnvironmentWithEntryModeDetailed` exposes the extraction context and IR together, while the existing compile entry points keep returning the same `IRModule` type.

The first tests cover the `Option ByteArray` and `Except UInt64 ByteArray` loop-output counter examples and `JsonTreeCommand.makeTree`.  The initial structured `Except` report showed two byte-array fold result slots with the same accumulator release offset, which identified the duplicate result-demand issue fixed in the next ownership change.  The report also distinguishes the source-level release in `JsonTreeCommand.insertOwned` from compiler-emitted releases, so source ownership boundaries and automatic cleanup can be inspected separately.

Checks run:

- [x] `lake build lean-wasm`
- [x] `node test/ownership_report.js` returned `checked 3 ownership report cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 3 ownership report cases`, `checked 695 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 94 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Option and Except foldlM

`Array.foldlM` and `ByteArray.foldlM` now compile for `Option` and `Except ε` when the callback is a direct lambda and the accumulator payload has a supported concrete layout.  The extractor represents the loop accumulator as the monad result value, stages each callback result through the existing multi-slot fold loop, and derives the loop stop flag from the staged tag.  A `none` or `Except.error` result stops the generated loop before later callback bodies run.

This uses the existing `Array.foldl` and `ByteArray.foldl` machinery instead of adding a new IR loop.  The implementation accepts the same accumulator payload classes as ordinary folds, including byte arrays and supported structures, while keeping `Id` `foldlM`, effectful callbacks, and escaping callback values rejected.  The correctness examples cover success, early failure that skips a later trap, an `Option ByteArray` accumulator, and `Array.attach.foldlM` with erased membership proofs.

Checks run:

- [x] `lake build LeanExe.Extract.Core lean-wasm LeanExe.Examples.Correctness` returned successfully.
- [x] `node test/core_correctness.js` returned `checked 680 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 84 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 680 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 84 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Interleaved Inline Specialization

Transparent inline specialization now supports static type, proof, and direct-lambda arguments interleaved with runtime arguments.  The specializer walks the helper lambda prefix in source order, substitutes static binders in place, preserves runtime binders in order, and lifts substituted static expressions across preserved runtime binders.  Inline extraction now appends the caller locals after helper runtime argument bindings, so a substituted direct lambda can capture a caller-local value without turning into a runtime closure.

Dependency collection now follows inline-only helper bodies far enough to add their supported callees to the compiled function set.  The inline-only helper itself remains uncompiled and specialized at the call site.  This fixes helper shapes such as `decodeRequiredField fields name (fun raw => ...)`, where the supported callees live inside a helper whose own type contains a function parameter.

The correctness corpus now includes `genericInterleavedLambdaHelper`, which calls a polymorphic helper with runtime arguments before a direct lambda that captures a local `bonus`.  The JSON decoder layer now includes `decodeRequiredField`, and `JsonObjectArrayDecode` uses it for scalar fields and for the nested `decodeArray` item decoder.

Checks run:

- [x] `lake build LeanExe.Extract.Core lean-wasm LeanExe.Examples.Correctness LeanExe.Examples.JsonObjectArrayDecode` returned successfully.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.genericInterleavedLambdaHelper --out .lake/build/generic-interleaved.wasm` returned successfully.
- [x] `build/tools/wasmtime/current/wasmtime run --invoke genericInterleavedLambdaHelper .lake/build/generic-interleaved.wasm` returned `22`.
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin-except --max-input-bytes 1024 --module LeanExe.Examples.JsonObjectArrayDecode --entry LeanExe.Examples.JsonObjectArrayDecode.transform --out .lake/build/json-object-array-decode.wasm` returned successfully.
- [x] `printf '%s' '{"items":[{"id":1,"weight":4},{"id":2,"weight":7}],"scale":3}' | build/tools/wasmtime/current/wasmtime run .lake/build/json-object-array-decode.wasm` returned `{"weighted":54,"count":2}`.
- [x] `node test/core_correctness.js` returned `checked 670 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node test/wasi_program.js` returned `checked 35 WASI program cases, 2 traps, and 7 rejections`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 79 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 670 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 79 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: JSON Object Array Decoding

The JSON decoder layer now has a generic `decodeArray` helper that accepts a direct decoder lambda and returns an array of decoded source-level values.  This required two compiler generalizations: transparent inline specialization now accepts direct-lambda static arguments before runtime arguments, and generated `Except` match helpers are recognized by locating the typed `Except` scrutinee even when Lean places type and motive parameters before it.  The lambda is substituted into the helper body, so the generated WASM still contains first-order code rather than a runtime closure.

`LeanExe.Examples.JsonObjectArrayDecode` decodes `{"items":[{"id":...,"weight":...}],"scale":...}` into source-defined `Item` and `Request` structures, rejects duplicate, missing, unknown, and mistyped fields, checks arithmetic overflow, and returns `{"weighted":...,"count":...}` through the WASI `Except` adapter.  The example keeps JSON decoding as ordinary Lean code over the recursive AST.

Checks run:

- [x] `lake build LeanExe.Extract.Core lean-wasm LeanExe.Examples.JsonObjectArrayDecode` returned successfully.
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin-except --max-input-bytes 1024 --module LeanExe.Examples.JsonObjectArrayDecode --entry LeanExe.Examples.JsonObjectArrayDecode.transform --out .lake/build/json-object-array-decode.wasm` returned successfully.
- [x] `printf '%s' '{"items":[{"id":1,"weight":4},{"id":2,"weight":7}],"scale":3}' | build/tools/wasmtime/current/wasmtime run .lake/build/json-object-array-decode.wasm` returned `{"weighted":54,"count":2}`.
- [x] `node test/wasi_program.js` returned `checked 35 WASI program cases, 2 traps, and 7 rejections`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 78 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 669 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 78 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Typed JSON Decode Helpers

The JSON AST now has a small `Except ByteArray` decoder layer in `LeanExe.Ascii.Json.Decode`.  It wraps parse, render, object lookup, required-field lookup, typed scalar assertions, exact field-set checks, and unsigned-integer array decoding without adding JSON-specific compiler behavior.  `LeanExe.Examples.JsonTypedDecode` uses that layer to decode a JSON object into a source-defined request structure, reject missing, duplicate, unknown, and mistyped fields, check arithmetic overflow, and return compact JSON through the WASI `Except` adapter.

Checks run:

- [x] `lake build LeanExe.Ascii.Json.Decode LeanExe.Examples.JsonTypedDecode` returned successfully.
- [x] `node test/wasi_program.js` returned `checked 29 WASI program cases, 2 traps, and 7 rejections`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 77 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 669 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 29 WASI program cases, 2 traps, and 7 rejections`, `checked 77 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Except Do-Notation Parser Shapes

The correctness corpus now covers parser-shaped `Except` do-notation that calls helpers using accepted pure `Id.run` cursor loops.  The new examples return a structured ok payload, a nonrecursive tagged ok payload, and a byte-array ok payload, and they check that an error result skips a later trapping computation.  No extractor change was needed; the existing first-order `Except` bind lowering and pure-loop extraction already accepted these checked forms.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness` returned successfully.
- [x] `node test/core_correctness.js` returned `checked 669 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 76 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 669 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 76 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Sparse User-Inductive Matches

Pure `Id.run do` examples now cover sparse matches over nonrecursive user inductives.  The correctness corpus has `if let Status.ok value := status`, a named catch-all `Status` arm that rematches the fallback value, a nullary-constructor `Mode` `if let`, and a `while` loop that reads `Array Status` elements and uses the same sparse match inside the loop body.  These examples cover the source style used for tagged status values without making the compiler know about `Status`.

The matcher classifier now recognizes generated sparse match helpers whose explicit arms are indexed by constructor result types and whose fallback arm receives the whole scrutinee type.  The value extractor binds that fallback arm to the reconstructed nonrecursive tagged value for each unmatched constructor path.  Sparse generated matches over recursive inductives remain rejected.  The loop-step extractor also beta-reduces first-order local continuation lambdas before classifying let-bound types, matching the existing ordinary value extractor behavior.

Checks run:

- [x] `lake build LeanExe.Extract.Core lean-wasm` returned successfully.
- [x] `node test/core_correctness.js` returned `checked 665 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 72 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 665 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 72 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Mutable Id Matches and If-let

Pure `Id.run do` examples now cover mutable assignments under `match` and `if let`.  The correctness corpus has an `Option` match that updates a scalar, an `if let some` assignment, a named catch-all `Option` arm that uses the fallback scrutinee value, a user-defined `Status` match that returns a tagged value, and a state-record update under an `Option` match.  These examples exercise the source shapes used by ordinary parser and transformer code without adding a source-level special case for parser programs.

The compiler change is in generated `Option` matcher recognition.  Lean may elaborate `if let some ...` and sparse `Option` matches to a local `match_` helper whose fallback arm receives the scrutinee rather than a unit argument.  The matcher classifier now treats an arm whose parameter has the `Option α` scrutinee type as the none/catch-all arm, and the extractor binds that parameter to an `Option.none` value on the none path.  The same binding rule is used in the restricted Nat-tail-recursion matcher path.

Checks run:

- [x] `lake build LeanExe.Extract.Core LeanExe.Examples.Correctness lean-wasm` returned successfully.
- [x] `node test/core_correctness.js` returned `checked 661 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 68 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 661 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 68 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Heap-field Id state records

Pure `Id.run do` examples now cover mutable state records that contain heap fields.  The correctness corpus has one parser-style `while` loop that carries `pos`, `out : ByteArray`, and `ok` in one structure, stops at a nondigit, and returns the byte output accumulated before the stop.  It also has a mutable state record that carries an internal `Array UInt64` and a counter through a `while` loop, updating array elements with the current counter value.

This slice adds coverage rather than a new compiler rule.  The existing internal structure layout, byte-array owner slots, internal array owner slots, generated structure matcher extraction, and pure-loop accumulator path already provide the required behavior.  The new examples make that support observable through Wasmtime and through the standard Lean comparison harness.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness` returned successfully.
- [x] `node test/core_correctness.js` returned `checked 656 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 63 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 656 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 63 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Parser-Style Id Cursor Loops

Pure `Id.run do` examples now cover parser-style cursor code.  The correctness corpus has a byte scanner that reads `input[pos]!`, stops on the first non-digit, and returns a structure; a byte-output loop that writes parsed digit values; an `Except UInt64 DigitState` parser status; and a mutable `Array UInt64` updated in a `while` loop before a `for` fold.  These examples exercise indexed reads, mutable cursors, mutable heap values, mutable arrays, explicit status, and loop-exit control in one source style.

The compiler change is in generated structure matcher extraction.  Lean carries several mutable locals through loops as nested `MProd` values, then may recover the locals through a generated matcher whose arm receives flattened fields such as `ok`, `pos`, and `sum`, rather than an immediate nested pair.  Structure match extraction now checks the arm lambda arity and, when it matches the flattened field count of nested single-constructor structures, binds those flattened fields directly.  Ordinary immediate-field structure matches keep their previous behavior.

Checks run:

- [x] `lake build LeanExe.Extract.Core LeanExe.Examples.Correctness lean-wasm` returned successfully.
- [x] `node test/core_correctness.js` returned `checked 654 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 61 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 654 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 61 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Ordinary Id Mutable Assignments

Pure `Id.run do` extraction now handles ordinary mutable-local code outside loop bodies.  Lean lowers nested assignment branches to local continuation lambdas that accept the current mutable locals and a `PUnit` sequencing value, then return an `Id` result.  The extractor now substitutes those local lambdas when they remain first-order, beta-reduces their direct applications, treats `PUnit` as the existing unit representation, and lowers `ite (Id α)` by extracting both branch values under a shared condition.

The correctness corpus now covers multiple scalar mutable locals under nested conditionals, structure return after assignment, `ByteArray` return after branch assignment, `Option` return after mutable status updates, and `Except` return after mutable status updates.  The standard Lean comparison self-test covers the same scalar, structure, tagged, and byte-array results.  The rejection corpus now includes a local function stored as data inside `Id.run`, so this change accepts Lean's generated local continuations without adding runtime closures.

Checks run:

- [x] `lake build LeanExe.Extract.Core LeanExe.Examples.Correctness lean-wasm` returned successfully.
- [x] `node test/core_correctness.js` returned `checked 650 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 57 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 650 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 57 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Pure While and Nested Id Loops

The extractor now accepts the checked Lean form behind source `while` loops.  Lean elaborates `while` in `Id.run do` to `ForIn.forIn` over `Lean.Loop`, whose step returns `ForInStep.done` to stop and `ForInStep.yield` to continue.  The IR now has `loopFoldMultiSlot` expression and statement forms that reuse the existing multi-slot accumulator layout without inventing a source-level loop syntax in the compiler.

Loop-body extraction now has a second path for ordinary pure `Id` computations that produce a `ForInStep` value.  The older parser still handles direct `yield`, `done`, `break`, `continue`, and simple conditional step shapes.  When the body contains nested pure loops or generated product and structure destructuring, the extractor materializes the `ForInStep` value once, reads its tag, selects the active accumulator payload, and carries the done flag through the same staged loop assignment path.

The correctness corpus now covers multiple mutable locals in a `for` loop, nested array `for` loops, scalar `while`, `while` with `break` and `continue`, a structure accumulator in `while`, nested `while`, and a byte-array result built in `while`.  The standard Lean comparison self-test covers the nested array loop, `while` with `break` and `continue`, and the byte-array `while` result.  This moves ordinary cursor and counter code closer to the intended first-order programming style while keeping the source language pure.

Checks run:

- [x] `lake build LeanExe.Extract.Core LeanExe.Wasm.Binary` returned successfully.
- [x] `lake build LeanExe.Examples.Correctness lean-wasm` returned successfully.
- [x] `node test/core_correctness.js` returned `checked 645 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 52 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 645 accepted, 29 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 52 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Parked Ownership Diagnostics

The next ownership follow-up should be diagnostic.  A proposed `lean-wasm ownership-report --module M --entry E` command should print, per extracted function, the result type, result owner slots, helper-result fresh-owner offsets, compiler-inserted releases, returned owner slots kept live, fold accumulator release offsets, and explicit `LeanExe.Runtime.release` sites.  Snapshot cases should include `byteArrayResultDropsOwnedTempStats`, `u64ListTailValue`, `JsonTreeCommand.makeTree`, and a fold-accumulator release case.

Broader recursive heap-result cleanup should wait for explicit provenance.  The compiler needs enough data to prove whether returned recursive roots own their children or borrow from a temporary, including arrays and byte-array owners inside the graph.  The current conservative recursive boundary is deliberate: nonrecursive result cleanup, accumulator releases, helper-result summaries, and source-level release boundaries cover the cases the compiler can justify today.

This note parks the memory-management topic so the next work can return to language expressiveness.  The most useful next target is broader Lean source support for local mutable-state style through checked `Id.run` and `do` forms.  That target would make parser, scanner, and command-transform examples shorter without adding runtime services.

## 2026-05-20: Nonrecursive Heap-Result Temporary Release

Heap-returning functions now have a limited compiler-emitted release path for dead nonrecursive heap temporaries.  During result materialization, the extractor protects owner slots that appear in the returned heap value, owner slots reached through borrowed root expressions, and heap arguments to returned helper-call results that may borrow from those arguments.  It may release a fresh nonrecursive owner slot, currently an internal `ByteArray` or `Array` owner, when that owner is absent from the protected set and the body has not already released it.

The implementation excludes recursive heap-result temporaries.  A broader recursive rule exposed unsound releases in existing JSON tree programs, where returned recursive values can contain borrowed children, arrays, and byte-array owners whose lifetime depends on retain and ownership-transfer details across several layouts.  Recursive heap temporaries still release in scalar-result functions, helper-result scalar callers, fold and loop accumulator replacement, and explicit source-level `LeanExe.Runtime.release` boundaries.

Checks run:

- [x] `lake build LeanExe.Extract.Core LeanExe.Examples.Correctness lean-wasm` returned successfully.
- [x] `node test/refcount.js` returned `checked 25 refcount cases`.
- [x] `node test/core_correctness.js` returned `checked 638 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 49 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 638 accepted, 29 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 49 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-18: Fold Accumulator Ownership Release

Loop-carried heap values now have a conservative compiler-emitted release path.  The extractor computes owner-slot offsets for the accumulator result type, including owner slots inside products, structures, sums, and nonrecursive tagged payloads.  It attaches a release offset to an `Array.foldl`, `ByteArray.foldl`, or accepted pure `for` loop only when the staged next accumulator slot is proven fresh by local allocation analysis and the body has not already released the old accumulator slot.

The WASM emitter now evaluates the loop body, stages the next accumulator slots, evaluates the loop-exit flag, releases the previous iteration's owned accumulator roots, and then copies staged values over the accumulator locals.  A loop releases a shared root only once when two owner slots hold the same pointer.  It skips the initial accumulator value, because ordinary Lean aliases can still refer to that value after the loop and the compiler does not yet prove that the initializer is unique.  This rule reclaims the common immutable-update pattern used by byte-array accumulators, array accumulators, and recursive-inductive accumulators without requiring source-level `LeanExe.Runtime.release` in the loop body.

The release rule remains local to supported loop and fold accumulator replacement.  Escaping heap-pointer results stay owned by the caller or host, and helper results that may borrow from heap arguments stay conservative unless the existing ownership-summary pass proves the relevant owner slot fresh.

Checks run:

- [x] `lake build LeanExe.Wasm.Binary` returned successfully.
- [x] `lake build lean-wasm` returned successfully.
- [x] `lake build LeanExe.Examples.Correctness lean-wasm` returned successfully.
- [x] `node test/core_correctness.js` returned `checked 636 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/refcount.js` returned `checked 24 refcount cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 636 accepted, 29 rejected, and 13 trapped cases`, `checked 24 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 47 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-18: Recursive Child Ownership Transfer

Recursive heap allocation now carries an owned-child mask in addition to the child-pointer mask.  The child-pointer mask still tells `release` which slots contain heap children, while the owned-child mask tells allocation which child pointers are already owned by the newly allocated parent.  Allocation retains child pointers that are borrowed and skips the retain for child pointers proven fresh by local allocation analysis or helper-result ownership summaries.

This makes recursive helper-result cleanup sound for scalar-result callers.  A helper may receive a recursive heap value, return a fresh recursive value that embeds both a fresh child and a borrowed input child, and the caller may release the temporary result after scalar traversal.  The refcount test covers that shape with a small binary tree and checks that all three recursive heap blocks become reusable.

The WASI tree examples exposed the matching source-level rule.  Immutable insertion shares untouched subtrees with the previous accumulator, so correct RC must retain those children and the old accumulator root must be released after replacement when the program owns that accumulator.  The extractor now preserves `let _ := LeanExe.Runtime.release value` as an ownership boundary, `JsonTreeCommand` uses that form when inserting into an owned accumulator, and the WASI tests check that explicit releases advance free counters without assuming that release and free counts are equal under sharing.

Checks run:

- [x] `lake build LeanExe.Extract.Core` returned successfully.
- [x] `lake build lean-wasm` returned successfully.
- [x] `node test/refcount.js` returned `checked 17 refcount cases`.
- [x] `node test/core_correctness.js` returned `checked 631 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/wasi_program.js` returned `checked 22 WASI program cases, 2 traps, and 7 rejections`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 631 accepted, 29 rejected, and 13 trapped cases`, `checked 17 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 47 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-18: Helper Result Ownership Summaries

The release pass now has per-helper ownership summaries for fresh array and byte-array result owner slots.  The compiler first extracts the reachable functions without summaries, computes a fixed-point summary over the extracted IR, then extracts again with those summaries available to the existing release insertion paths.  This removes the old rule that suppressed helper-call cleanup whenever a callee had any heap-bearing parameter.

The summary pass starts with parameters unowned, follows assignments, local lets, helper calls, branches, releases, and simple loops conservatively, and marks a result owner slot only when the result expression is fresh on every path.  At this checkpoint it applied to array and byte-array owner offsets, including structured results that contain those owners.  The later recursive child ownership work extended the same summary path to recursive-inductive result slots.

Checks run:

- [x] `lake build LeanExe.Extract.Core` returned successfully.
- [x] `lake build lean-wasm` returned successfully.
- [x] `node test/refcount.js` returned `checked 16 refcount cases`.
- [x] `node test/core_correctness.js` returned `checked 629 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 629 accepted, 29 rejected, and 13 trapped cases`, `checked 16 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 47 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-15: Internal Array Owner Slots

Internal `Array α` values now carry two slots: an owner root and the visible array pointer.  The public ABI remains one array pointer, and public or WASI-adapter arrays enter compiled code with owner `0`.  Nested arrays stored inside fixed-width values now have enough ownership metadata for release to follow them without treating borrowed public arrays as owned roots.

The array child mask now marks nested `Array` owner slots in the same way it marks `ByteArray` owners and recursive-inductive child pointers.  Array-copying operations retain nested-array owners when they share elements, while operations that insert freshly constructed arrays transfer the owned root into the new array.  Array operations that can return the original input preserve the original owner slot, so no-op updates over borrowed public arrays remain borrowed.

The extractor no longer treats an arbitrary scalar as a complete array value during materialization.  Array values must carry owner and pointer slots, which exposed and fixed `Array.swapAt`'s updated-array result.  Local materialization also has a specific owned-array path to avoid creating an alias that would be released twice after an explicit `LeanExe.Runtime.release`.  The WASI argv adapters now pass owner `0` plus the visible array pointer to entries that accept `Array ByteArray`.

Checks run:

- [x] `lake build lean-wasm` returned successfully.
- [x] `node test/refcount.js` returned `checked 11 refcount cases`.
- [x] `node test/core_correctness.js` returned `checked 614 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/wasi_program.js` returned `checked 22 WASI program cases, 2 traps, and 7 rejections`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 614 accepted, 29 rejected, and 13 trapped cases`, `checked 11 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 38 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-15: Heap-backed Equality Lowering

Equality lowering now includes `ByteArray` and fixed-width `Array α` values when `α` also has supported equality.  `ByteArray` equality binds both pointer-length pairs once, compares lengths first, and then scans bytes in order.  Array equality binds both array pointers once, compares lengths first, loads each element into compiler-managed local slots, and evaluates the same type-directed structural equality expression used for standalone values.

The implementation keeps recursive-inductive equality rejected.  Arrays of recursive-inductive elements therefore remain outside supported equality, even though recursive values can still appear in internal arrays for traversal and storage.  Supported array equality covers scalar elements, nested arrays, byte-array elements, structures containing byte arrays, and nonrecursive tagged values whose payload fields all support equality.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness` returned successfully.
- [x] `node test/core_correctness.js` returned `checked 610 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 38 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 610 accepted, 29 rejected, and 13 trapped cases`, `checked 5 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 38 standard Lean comparison cases`, and `checked 56 cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.byteArrayStructureArrayEquality --out /tmp/byteArrayStructureArrayEquality.wat` returned successfully.
- [x] `build/tools/wasmtime/current/wasmtime --invoke byteArrayStructureArrayEquality /tmp/byteArrayStructureArrayEquality.wat` returned `1`.

## 2026-05-15: Recursive Pure Result Comparisons

The standard Lean comparison self-test now exercises heap-shaped pure results through `pure-bytes`.  `LeanExe.Examples.Correctness` defines small source-level serializers for a custom recursive list, ordinary `List UInt64`, an array-child tree, a binary tree, and a mutual-recursive JSON-like value.  The comparison tool now serializes producer results for custom-list tail selection, `List` append, reverse, map, and filter, tree construction, binary-tree construction, and mutual-recursive object construction, then compares those bytes against standard Lean.

The self-test also compares the real JSON AST parser as a pure value producer.  The case calls `LeanExe.Ascii.Json.parseBytes` on a nested object, serializes `some value` through `LeanExe.Ascii.Json.render`, and compares the rendered bytes with the WASM wrapper output.  This gives standard-Lean coverage for a recursive AST result without depending on JavaScript heap inspection.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node tools/compare-standard.js --self-test` returned `checked 33 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 596 accepted, 31 rejected, and 13 trapped cases`, `checked 5 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 33 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-15: Serialized Pure Standard Lean Comparison

`tools/compare-standard.js` now supports `pure-bytes` mode for concrete pure calls whose results need byte-level serialization.  The tool generates a temporary Lean wrapper under `LeanExe/StandardCompare`, compiles that wrapper with `compile-wasi`, runs the resulting WASI command with Wasmtime, and compares stdout and stderr with a standard Lean runner that evaluates the same serializer.  The serializer sees the target result as `__leanexeValue` and must produce `ByteArray`, so heap-backed results can be compared without adding JavaScript-specific memory inspectors for each source type.

The self-test covers `ByteArray` returns, branch-selected byte arrays, structures containing arrays, structures containing arrays of structures, and byte-producing state structures returned by array and byte-array folds.  The array serializers use `Array.foldl` rather than unchecked indexing, which keeps the generated wrapper inside ordinary Lean source and avoids adding artificial `Inhabited` instances to example types.  `LeanExe/StandardCompare` is ignored because failed comparison runs may leave generated wrapper sources for diagnosis.

At this checkpoint, the correctness fixtures included valid Lean programs that compared unsupported heap-backed values: `Array UInt64`, `ByteArray`, and a recursive inductive.  Each case reached the extractor and failed with an explicit unsupported-equality diagnostic.  The later heap-backed equality work superseded the array and byte-array part of this boundary, while recursive inductive equality remains rejected.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.rejectArrayEquality --out /tmp/rejectArrayEquality.wasm` rejected with `unsupported equality type: LeanExe.IR.Ty.array (LeanExe.IR.Ty.u64)`.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.rejectByteArrayEquality --out /tmp/rejectByteArrayEquality.wasm` rejected with `unsupported equality type: LeanExe.IR.Ty.byteArray`.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.rejectRecursiveInductiveEquality --out /tmp/rejectRecursiveInductiveEquality.wasm` rejected with `unsupported equality type: LeanExe.IR.Ty.recVariant`.
- [x] `node test/core_correctness.js` returned `checked 596 accepted, 31 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 24 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 596 accepted, 31 rejected, and 13 trapped cases`, `checked 5 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 24 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-15: Pure Standard Lean Comparison

`tools/compare-standard.js` now supports a `pure` mode for library exports in addition to the existing WASI command modes.  Pure mode compiles the selected entry with `compile`, invokes the exported function through `wasmtime --invoke`, and compares the printed result slots with a generated standard-Lean runner.  The runner evaluates a Lean call expression and prints a caller-provided `Array UInt64` slot expression, which makes flattened structure parameters and multi-slot structure or tagged results explicit in the test case rather than inferred by JavaScript.

The self-test now includes scalar results, bounded `Nat` results, structure results, flattened structure parameters, tagged results, flattened tagged parameters, and structural equality over products, structures, nonrecursive tagged values, and `Option` values.  It deliberately avoids examples whose purpose is to prove LeanExe's demand analysis skips a trapping expression, because the standard Lean runner may evaluate that expression before the value reaches the inspected field or tag.

Checks run:

- [x] `node tools/compare-standard.js --self-test` returned `checked 18 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 596 accepted, 28 rejected, and 13 trapped cases`, `checked 5 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 18 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-15: Structural Equality Lowering

The extractor now lowers equality through a type-directed value comparison instead of routing every `BEq.beq`, `bne`, and `Eq` proposition through scalar extraction.  The supported equality fragment covers `Unit`, scalar values, products, structures, internal sums, `Option`, `Except`, and nonrecursive tagged values whose runtime fields also support equality.  The lowering compares fields in source order and compares tagged values by constructor tag before active payload fields, preserving short-circuit behavior for later fields and inactive constructor payloads.

At this checkpoint, array equality, `ByteArray` equality, and recursive-inductive equality remained unsupported because they needed explicit element iteration or heap traversal semantics.  The correctness cases covered product equality, structure equality, nested structures, proposition equality through `DecidableEq`, nonrecursive-inductive equality, `Option` equality over structures, and short-circuit cases whose skipped payloads would trap if evaluated.  The later heap-backed equality work superseded the array and byte-array limitation while retaining the recursive-inductive rejection.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 596 accepted, 28 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 596 accepted, 28 rejected, and 13 trapped cases`, `checked 5 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 8 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-15: Option and Except Do Notation

The extractor now recognizes `Option` and `Except ε` as supported monads for overloaded `Pure.pure`, `Bind.bind`, and `Functor.map`.  `Option` and `Except` `do` notation lowers to the same first-order tag and payload representation as the existing direct `Option.bind`, `Option.map`, `Except.bind`, and `Except.map` paths when callbacks are direct lambdas and payload types are concrete supported types.  `Functor.map` is now blocked from transparent unfolding, so Lean's class projection for the selected instance does not become a runtime function value.

The JSON examples now use the new source style where it improves the program shape.  `LeanExe.Examples.JsonAdd.parseInput` and `LeanExe.Examples.JsonCollatzLength.lengthInput?` use `Option` `do` notation, while `LeanExe.Examples.JsonGcd.transformAscii` uses `Except` `do` notation through a small `requireGcdInput` helper.  The standard Lean comparison self-test now includes the JSON add and JSON Collatz command entries.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness lean-wasm`
- [x] `node test/core_correctness.js` returned `checked 582 accepted, 28 rejected, and 13 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 94 report classification cases`.
- [x] `lake build LeanExe.Examples.JsonAdd LeanExe.Examples.JsonCollatzLength LeanExe.Examples.JsonGcd lean-wasm`
- [x] `node test/json_double.js` returned `checked 48 json program cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 8 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 582 accepted, 28 rejected, and 13 trapped cases`, `checked 5 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 8 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-15: Standard Lean Comparison Batch

The standard Lean comparison tool matched generated WASM for the main command-shaped examples that do not read LeanExe runtime counters.  The batch covered plain byte output, JSON field parsing and rendering, checked arithmetic failure encoded as JSON, Collatz JSON, GCD success and failure through `Except`, JSON tree construction, JSON tree search with stdin plus argv, and argv-only byte handling.

Checks run:

- [x] `LeanExe.Examples.JsonDouble.transform` under `stdin` with `{"n":21}`.
- [x] `LeanExe.Examples.JsonAdd.transform` under `stdin` with `{"a":19,"b":23}`.
- [x] `LeanExe.Examples.JsonAdd.transform` under `stdin` with `{"a":18446744073709551615,"b":1}`.
- [x] `LeanExe.Examples.JsonCollatzLength.transform` under `stdin` with `{"collatzLengthFor":41}`.
- [x] `LeanExe.Examples.JsonGcd.transform` under `stdin-except` with `[1,6,4,100,33,5,5,20]`.
- [x] `LeanExe.Examples.JsonGcd.transform` under `stdin-except` with `[]`.
- [x] `LeanExe.Examples.JsonTreeCommand.makeTree` under `stdin-except` with `[1,6,4,100,33,5,5,20]`.
- [x] `LeanExe.Examples.JsonTreeCommand.searchTree` under `stdin-argv-except` with a nested tree and search values `4` and `7`.
- [x] `LeanExe.Examples.ByteArrayPrograms.argvFirstLast` under `argv-except` with `alpha` and `omega`.
- [x] `LeanExe.Examples.Correctness.byteArrayAppendReturn` under `wasi`.

## 2026-05-15: Standard Lean Comparison Tool

`tools/compare-standard.js` compares a command-shaped entry against official Lean execution.  It generates a temporary Lean runner under `.lake/build/standard-compare`, runs that runner with `lake env lean --run`, compiles the same entry through the selected LeanExe WASI mode, runs the generated WASM with Wasmtime, and compares exit status, stdout, and stderr byte-for-byte.  The first supported modes are the byte-oriented command shapes: `wasi`, `stdin`, `stdin-except`, `argv-except`, and `stdin-argv-except`.

The tool deliberately treats standard Lean as the reference program, not as another hand-written expected-output fixture.  The runner writes standard Lean output to binary files with `IO.FS.writeBinFile`, which avoids text-encoding behavior in `IO.print`.  Programs that inspect `LeanExe.Runtime` counters are outside this comparison because standard Lean uses stub definitions while generated WASM reads runtime counters.

Checks run:

- [x] `node tools/compare-standard.js --self-test` returned `checked 6 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 574 accepted, 28 rejected, and 13 trapped cases`, `checked 5 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 6 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-15: Growable Runtime Allocator

The runtime allocator now calls WASM `memory.grow` when neither the free list nor the current heap range can satisfy an allocation.  The generated memory still starts at 16 pages, and `reset()` still rewinds the heap to byte offset `4096`, but large library-mode allocations and compiled-code allocations can grow the module memory instead of trapping at the initial page boundary.  `test/refcount.js` now allocates a block as large as the initial memory, verifies that the memory grew, and writes the last byte of the returned range.

This changes the failure mode for large single requests.  Reference counting still matters because memory growth is bounded by the host and because long computations can allocate more live data than they need if dead generations are not released.  The JSON GC tree rewrite example now accepts `rounds <= 40`; a Wasmtime run for `{"depth":8,"rounds":40,"salt":17,"search":12345}` returned `nodeCount:255`, `height:8`, `allocsAfterInitial:575`, `freesAfterRounds:20440`, `releasesAfterFinal:20951`, and `freesAfterFinal:20951`.

Checks run:

- [x] `lake build lean-wasm`
- [x] `node test/refcount.js` returned `checked 5 refcount cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.byteArrayStringConstReturn --out .lake/build/refcount/byteArrayStringConstReturn.grow.wat`
- [x] `build/tools/wasmtime/current/wasmtime --invoke alloc .lake/build/refcount/byteArrayStringConstReturn.grow.wat 1048576` returned `4096`.
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin-except --max-input-bytes 1024 --module LeanExe.Examples.JsonGcTreeRewrite --entry LeanExe.Examples.JsonGcTreeRewrite.transform --out .lake/build/wasi-programs/jsonGcTreeRewrite.stdin-except.wasi.wasm`
- [x] `printf '{"depth":8,"rounds":40,"salt":17,"search":12345}' | build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/jsonGcTreeRewrite.stdin-except.wasi.wasm`
- [x] `printf '{"depth":8,"rounds":41,"salt":17,"search":12345}' | build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/jsonGcTreeRewrite.stdin-except.wasi.wasm` returned `{"error":1}`.
- [x] `node test/wasi_program.js` returned `checked 22 WASI program cases, 2 traps, and 7 rejections`.
- [x] `node test/core_correctness.js` returned `checked 574 accepted, 28 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 574 accepted, 28 rejected, and 13 trapped cases`, `checked 5 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, and `checked 56 cases`.

## 2026-05-15: JSON GC Tree Rewrite Benchmark

`LeanExe.Examples.JsonGcTreeRewrite` is a JSON-to-JSON WASI command that builds a balanced source-level tree, rewrites whole tree generations, releases the previous root after each rewrite, and releases the final root after computing metrics.  The input object contains `depth`, `rounds`, `salt`, and `search`.  The current accepted workload is `1 <= depth <= 8` and `rounds <= 40`, which exercises thousands of recursive-inductive frees.

The first implementation built a linear tree through a fuel-recursive structure accumulator.  That shape compiled but produced unusable runtime behavior once the tree passed roughly twenty nodes, because the accumulator carried a recursive heap root through every loop step.  The benchmark now builds the initial tree through direct balanced recursion by depth, then uses generation-level release boundaries.  A Wasmtime run for `{"depth":8,"rounds":20,"salt":17,"search":12345}` returned `nodeCount:255`, `height:8`, `allocsAfterInitial:575`, `freesAfterRounds:10220`, `releasesAfterFinal:10731`, and `freesAfterFinal:10731`.

Checks run:

- [x] `lake build LeanExe.Examples.JsonGcTreeRewrite`
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin-except --max-input-bytes 1024 --module LeanExe.Examples.JsonGcTreeRewrite --entry LeanExe.Examples.JsonGcTreeRewrite.transform --out .lake/build/wasi-programs/jsonGcTreeRewrite.stdin-except.wasi.wasm`
- [x] `printf '{"depth":8,"rounds":20,"salt":17,"search":12345}' | build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/jsonGcTreeRewrite.stdin-except.wasi.wasm`
- [x] `printf '{"depth":8,"rounds":21,"salt":17,"search":12345}' | build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/jsonGcTreeRewrite.stdin-except.wasi.wasm` returned `{"error":1}`.
- [x] `node test/wasi_program.js` returned `checked 22 WASI program cases, 2 traps, and 7 rejections`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 574 accepted, 28 rejected, and 13 trapped cases`, `checked 4 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, and `checked 56 cases`.

## 2026-05-15: Runtime Counters and Merge-Tree Release Demo

The runtime now maintains allocation, retain, release, and free counters in mutable WASM globals.  `LeanExe.Runtime.allocCount`, `retainCount`, `releaseCount`, and `freeCount` compile to reads of those globals, while `LeanExe.Runtime.release` compiles to an explicit release for monomorphic recursive-inductive heap roots.  Source-level release keeps a manual ownership precondition: the released root and any heap nodes it shares with live values must not be used after the call.

Recursive-inductive heap allocation now records a child-pointer mask in the object header.  The release runtime follows that mask and recursively releases child pointers before putting the current object on the free list.  Array objects have a mask slot in the runtime header, but the compiler still emits zero for array masks, so array child release remains future work.

`LeanExe.Examples.JsonMergeTreeCommand` reads two JSON integer arrays, builds one source-level binary-search tree for each, constructs a third merged tree by copying values from the first two trees, and then releases the first two roots.  The command emits the merged tree plus GC counters, and its companion search command reads the intermediate object and searches the final tree.  A Wasmtime run for `[[1,6,4,100],[33,5,5,20]]` reported `allocs:145`, `freesBefore:0`, `freesAfterFirst:9`, `freesAfterSecond:18`, and `releasesAfterSecond:18` before search.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.JsonMergeTreeCommand`
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin-except --max-input-bytes 4096 --module LeanExe.Examples.JsonMergeTreeCommand --entry LeanExe.Examples.JsonMergeTreeCommand.makeMergedTree --out .lake/build/wasi-programs/makeMergedTree.stdin-except.wasi.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin-argv-except --max-input-bytes 8192 --max-args 8 --max-argv-bytes 256 --module LeanExe.Examples.JsonMergeTreeCommand --entry LeanExe.Examples.JsonMergeTreeCommand.searchMergedTree --out .lake/build/wasi-programs/searchMergedTree.stdin-argv-except.wasi.wasm`
- [x] `printf '[[1,6,4,100],[33,5,5,20]]' | build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/makeMergedTree.stdin-except.wasi.wasm`
- [x] `printf '[[1,6,4,100],[33,5,5,20]]' | build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/makeMergedTree.stdin-except.wasi.wasm | build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/searchMergedTree.stdin-argv-except.wasi.wasm 4` returned `{"found":true,"allocs":849,"releases":0,"frees":0}`.
- [x] `node test/wasi_program.js` returned `checked 20 WASI program cases, 2 traps, and 7 rejections`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 574 accepted, 28 rejected, and 13 trapped cases`, `checked 4 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 20 WASI program cases, 2 traps, and 7 rejections`, and `checked 56 cases`.

## 2026-05-14: JSON Tree Example Cleanup

`LeanExe.Examples.JsonTreeCommand` now renders the intermediate tree through the JSON AST renderer instead of assembling byte-level object fragments by hand.  The example keeps the attached-field fold in `decodeTree`, because that spelling exposes the field-membership proof Lean needs for structural recursion and matches the well-founded-recursion shape the compiler already supports.  A getter-based recursive decoder is valid Lean, but Lean lowers it through a generated well-founded shape outside the current extractor.

`LeanExe.Ascii.Json.Value` now provides reusable object helpers for nonrecursive AST consumers: `countField`, `getUniqueField?`, `nameInArray`, and `allFieldNamesIn`.  The helper theorem for unique field lookup records that a returned field value is structurally smaller than the containing field array, which is useful for future recursive decoders once the extractor accepts the corresponding generated shape.

Checks run:

- [x] `lake build LeanExe.Examples.JsonTreeCommand`
- [x] `node test/wasi_program.js`

## 2026-05-14: AST JSON Parser and Tree Pipeline

`LeanExe.Ascii.Json.Value` adds an ASCII-only JSON AST with `null`, booleans, unsigned `UInt64` numbers, restricted unescaped strings, arrays, and objects.  The parser is a single bounded recursive dispatcher over a request type, so recursive descent uses one accepted Nat-recursive helper with an explicit parse mode and tagged parse result.  The tree command now parses both the input array and the intermediate tree JSON through that AST, and it emits the tree through JSON writer helpers instead of embedding punctuation fragments in the example.

`JsonTreeCommand.buildTree` uses `Array.foldl` over parsed JSON array elements.  It no longer carries an explicit fuel counter for that scan, because the compiler supports `Array.foldl` with a supported structure accumulator and direct-lambda folder.  `JsonTreeCommand.searchTree` now decodes the parsed JSON AST into the source-level `Tree` type before searching.  The search is ordinary structural recursion over `Tree`, so the example no longer needs a bounded search through object-field lookup.

The extractor now represents materialized internal values as `LocalLet` blocks when a fold body or source `let` produces a multi-slot structure.  Fold IR nodes carry those blocks and the WASM emitter runs them once per iteration before assigning the next accumulator slots.  The local-let liveness pass removes definitions that the demanded projection or returned value does not use, preserving Lean's lazy behavior for unused fields while still avoiding repeated recursive calls in structured fold bodies.

The compiler now accepts expression-position calls to the generated Nat-recursive handle by emitting an ordinary WASM call with decremented fuel.  Tail-position calls still lower to the existing loop form, so parser loops keep the efficient path when the source branch is a plain continuation.  Fuel-recursive steps that match a recursive inductive now fall back to exit-expression lowering, which allows bounded search helpers to inspect recursive AST values without treating the match as loop control.

Checks run:

- [x] `lake build LeanExe.Ascii.Json.Value`
- [x] `lake build LeanExe.Examples.JsonTreeCommand`
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin-except --max-input-bytes 4096 --module LeanExe.Examples.JsonTreeCommand --entry LeanExe.Examples.JsonTreeCommand.makeTree --out build/make-tree.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin-argv-except --max-input-bytes 8192 --max-args 8 --max-argv-bytes 256 --module LeanExe.Examples.JsonTreeCommand --entry LeanExe.Examples.JsonTreeCommand.searchTree --out build/search-tree.wasm`
- [x] `printf '%s' '[1,6,4,100,33,5,5,20]' | build/tools/wasmtime/current/wasmtime run build/make-tree.wasm | build/tools/wasmtime/current/wasmtime run build/search-tree.wasm 4` returned `{"found":true}`.
- [x] `printf '%s' '[1,6,4,100,33,5,5,20]' | build/tools/wasmtime/current/wasmtime run build/make-tree.wasm | build/tools/wasmtime/current/wasmtime run build/search-tree.wasm 7` returned `{"found":false}`.
- [x] `node test/wasi_program.js` returned `checked 19 WASI program cases, 2 traps, and 7 rejections`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 574 accepted, 28 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 19 WASI program cases, 2 traps, and 7 rejections`, and `checked 56 cases`.

## 2026-05-14: JSON Array GCD Command

`LeanExe.Ascii.Json.parseArrayRanges` scans a JSON array and returns raw element ranges.  It is a JSON-level scanner: callers decide how to interpret each element.  `LeanExe.Examples.JsonGcd.transform` uses that scanner to read a nonempty array of decimal `UInt64` values from stdin under `compile-wasi-stdin-except`, computes their GCD, and writes `{"gcd":N}` to stdout.

Checks run:

- [x] `lake build LeanExe.Examples.JsonGcd`
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin-except --max-input-bytes 1024 --module LeanExe.Examples.JsonGcd --entry LeanExe.Examples.JsonGcd.transform --out .lake/build/json-gcd.wasm`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime run .lake/build/json-gcd.wasm < /tmp/leanexe-json-gcd-input.json`
- [x] `node test/wasi_program.js`
- [x] `node test/run_all.js`

## 2026-05-14: JSON Example Cleanup

`LeanExe.Examples.JsonDouble` and `LeanExe.Examples.JsonAdd` use `Ascii.Json.getUInt64Field` for input and `Ascii.Json.object1UInt64` for output.  Both examples share the library field scanner and object generator.  Their behavior matches the documented limited JSON API: requested fields are order-independent, unknown supported values may be skipped, and malformed input or arithmetic overflow returns `{"error":1}`.

Checks run:

- [x] `lake build LeanExe.Examples.JsonDouble LeanExe.Examples.JsonAdd LeanExe.Examples.JsonCollatzLength LeanExe.Examples.JsonTools`
- [x] `node test/json_double.js`
- [x] `node test/run_all.js`

## 2026-05-06

The repository started with `plan.md` only.  The first implementation step creates a Lake package pinned to Lean 4.29.1, because elan reports that toolchain as installed and active.  No third-party Lean, JavaScript, or Wasm dependencies were added.

The initial executable target is narrow by design.  It supports the checked Lean declaration `LeanExe.Examples.AsciiDigits.validate : ByteArray -> Bool`, lowers it to a byte-range validator, and emits a standalone Wasm module with `memory`, `alloc`, `reset`, and `validate` exports.  Wasm compilation from the generic report, monomorphization, and typeclass specialization remain unimplemented.

Authoritative references used:

| Topic | Reference |
| ----- | --------- |
| Installed Lean toolchain | `elan show` |
| Lake project syntax | `lake init LeanExe exe.lean` template in `/tmp/lake-template-check` |
| Lean `ByteArray` API | Local Lean `#check` commands against Lean 4.29.1 |
| WebAssembly binary encoding | WebAssembly Core Specification binary format |
| Wasmtime release artifacts | https://github.com/bytecodealliance/wasmtime/releases |

Current plan:

- [x] Create a Lake package and project root.
- [x] Add a byte-array validator with a Lean soundness theorem.
- [x] Add a small core IR and evaluation semantics.
- [x] Add proof-erasure and lowering correctness lemmas for the first boundary.
- [x] Add a Wasm emitter for the lowered validator.
- [x] Add a Node host runner and fuzz differential harness.
- [x] Build the project with Lake: `lake build`.
- [x] Emit the report and Wasm module: `.lake/build/bin/lean-wasm emit --out build/validate.wasm`, `.lake/build/bin/lean-wasm wat --out build/validate.wat`, and `.lake/build/bin/lean-wasm report --out build/extraction-report.txt`.
- [x] Run Lean/Wasm differential tests: `node test/fuzz_validate.js build/validate.wasm 200`.

## 2026-05-06: Checked-Environment Report

The next implementation step adds `spec.md` and a checked-environment report path.  The report uses Lean’s `importModules` API, `Environment.find?`, `ConstantInfo`, and `Expr.getUsedConstants` from the installed Lean 4.29.1 toolchain.  It imports a compiled module, finds an entry constant, expands project-local dependencies by root namespace, and records external dependencies as a classified frontier.

The report does not claim generic compilation.  It classifies declarations so the next compiler step has concrete blockers rather than an unstructured failure.  The current classifier detects unsupported effects, higher-order argument types, polymorphic declarations, typeclass instance dependencies, external library operations, `unsafe`, `partial`, opaque constants, axioms, quotients, inductives, constructors, and recursors.

Commands run:

- [x] `lake build`
- [x] `.lake/build/bin/lean-wasm report --module LeanExe.Examples.AsciiDigits --entry LeanExe.Examples.AsciiDigits.validate --out build/env-report.txt`
- [x] `.lake/build/bin/lean-wasm report --module Main --entry main`

## 2026-05-06: Collatz Demo

`LeanExe.Examples.Collatz.steps : UInt64 -> UInt64` computes Collatz steps with a `10000`-step fuel bound.  The bound avoids `partial` recursion and avoids assuming the global Collatz conjecture.  The first Collatz Wasm emitter used a Collatz-specific byte emitter.  That path was removed.  The current path uses `lean-wasm compile --module <module> --entry <name> --out <path>`, which loads checked declarations, extracts the supported first `UInt64` fragment into `LeanExe.IR.Core`, and emits Wasm from that IR.

Planned checks:

- [x] `lake build`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Collatz --entry LeanExe.Examples.Collatz.steps --out build/collatz.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Collatz --entry LeanExe.Examples.Collatz.steps --out build/collatz.wat`
- [x] `.lake/build/bin/lean-wasm collatz-eval --input 27`
- [x] Run `build/collatz.wasm` with Wasmtime 36.0.9 from `/tmp`: `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke collatz_steps build/collatz.wasm 27`.

Limitation at that checkpoint: the generic compiler fragment supported only monomorphic first-order functions returning `UInt64`, `UInt64` and bounded `Nat` parameters represented as Wasm `i64`, primitive arithmetic, direct calls, `if`, boolean equality and disjunction, and tail recursion over a decreasing `Nat` fuel argument.  It did not lower arbitrary Lean expressions, data structures, pattern matching over user inductives, arrays, byte arrays, typeclasses beyond the primitive patterns it recognized, or IO.  `compile-wat` printed WAT from the same IR used by binary emission.  The verification pass compared Lean and Wasmtime for `27`, `989345275647`, `bench 27 10`, and `bench 989345275647 3`.

## 2026-05-06: Collatz Timing

OEIS A284668 lists `989345275647` as the smallest number below `10^12` with the largest total stopping time in that range.  A local arbitrary-precision check gives `1348` steps and a maximum trajectory value of `1219624271099764`, which fits in `UInt64`.

The timing comparison used `collatz_bench(n, iters)`, which repeats the computation inside the Lean executable or inside the Wasm module and returns the sum of all step counts.  This avoided measuring one process start per Collatz sequence.  These timing notes predate the generic compiler path and should be rerun before serving as current benchmark evidence.

Superseded commands run:

- [x] `lake build`
- [x] `.lake/build/bin/lean-wasm collatz-emit --out build/collatz.wasm`
- [x] `.lake/build/bin/lean-wasm collatz-bench --input 27 --iters 10000000`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke collatz_bench build/collatz.wasm 27 10000000`
- [x] `.lake/build/bin/lean-wasm collatz-bench --input 63728127 --iters 1000000`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke collatz_bench build/collatz.wasm 63728127 1000000`
- [x] `.lake/build/bin/lean-wasm collatz-bench --input 989345275647 --iters 1000000`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke collatz_bench build/collatz.wasm 989345275647 1000000`

## 2026-05-06: Generic UInt64 Compiler Fragment

`LeanExe.IR.Core` is now the generic executable IR for the first compiler fragment.  `LeanExe.Extract.Core` loads checked declarations from a Lean environment, collects supported project-local function dependencies, extracts the accepted `UInt64` and bounded-`Nat` fragment, and emits through `LeanExe.Wasm.Binary.CoreWasm`.  Collatz now compiles through `lean-wasm compile --module LeanExe.Examples.Collatz --entry LeanExe.Examples.Collatz.steps --out build/collatz.wasm`; there is no `LeanExe.Extract.Collatz` compiler path.

At this checkpoint, the first fragment supported monomorphic first-order functions returning `UInt64`, `UInt64` and bounded `Nat` parameters represented as Wasm `i64`, numeric literals, primitive `UInt64` arithmetic, `if`, boolean equality, boolean conjunction and disjunction, direct calls, and tail recursion over a decreasing `Nat` fuel argument.  Unsupported code failed during extraction with a reason.  Source-to-IR correctness remained unproved.

Checks run:

- [x] `lake build`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Collatz --entry LeanExe.Examples.Collatz.steps --out build/collatz.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Collatz --entry LeanExe.Examples.Collatz.steps --out build/collatz.wat`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Collatz --entry LeanExe.Examples.Collatz.bench --out build/collatz-bench.wasm`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke steps build/collatz.wasm 27`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke steps build/collatz.wasm 989345275647`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke bench build/collatz-bench.wasm 27 10`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke bench build/collatz-bench.wasm 989345275647 3`
- [x] `lake build LeanExe.Examples.Arithmetic`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Arithmetic --entry LeanExe.Examples.Arithmetic.affine --out build/affine.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Arithmetic --entry LeanExe.Examples.Arithmetic.choose --out build/choose.wasm`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke affine build/affine.wasm 5 11`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke choose build/choose.wasm 0 41`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke choose build/choose.wasm 8 41`
- [x] `node test/fuzz_validate.js build/validate.wasm 200`

## 2026-05-06: Naive Integer Map

`LeanExe.Examples.IntMap` is a simple open-addressed table from `UInt64` keys to `UInt64` values.  It uses 256 slots, stores each slot as adjacent key and value cells in an `Array UInt64`, reserves key `0` as empty, inserts keys `1` through `100`, maps key `k` to `k * 10 + 7`, and exports `query` and `checksum`.  `checksum` sums all 100 mapped values and returns `51200`.

The example required generic array support in the checked-declaration compiler.  At this checkpoint, the IR had `Array UInt64` pointer values, zero-filled allocation, indexed loads, and indexed stores.  The extractor recognized `Array.replicate n 0`, `Array.get!Internal`, `Array.set!`, boolean-valued helper functions represented as `0` or `1`, and zero-argument project declarations used as constants.  It rejected nonzero `Array.replicate` fills, because the Wasm lowering did not initialize arbitrary values.

That initial array lowering mutated Wasm memory in place and assumed linear use of arrays across updates.  That matched the integer-map example, but it did not implement Lean array alias semantics.  The later copy-on-write array section supersedes this lowering.

Checks run:

- [x] `lake build`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.IntMap --entry LeanExe.Examples.IntMap.query --out .lake/build/intmap-query.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.IntMap --entry LeanExe.Examples.IntMap.query --out .lake/build/intmap-query.wat`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.IntMap --entry LeanExe.Examples.IntMap.checksum --out .lake/build/intmap-checksum.wasm`
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke query .lake/build/intmap-query.wasm 1` returned `17`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke query .lake/build/intmap-query.wasm 100` returned `1007`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke query .lake/build/intmap-query.wasm 101` returned `0`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke checksum .lake/build/intmap-checksum.wasm` returned `51200`.
- [x] `lake env lean --stdin` with `#eval LeanExe.Examples.IntMap.query 1`, `#eval LeanExe.Examples.IntMap.query 100`, `#eval LeanExe.Examples.IntMap.query 101`, and `#eval LeanExe.Examples.IntMap.checksum` returned `17`, `1007`, `0`, and `51200`.

## 2026-05-06: Next Prime

`LeanExe.Examples.Prime.next : UInt64 -> UInt64` returns the first prime greater than the input within a fixed search fuel of `100000` candidate values.  It uses a naive divisor scan from `2` to `n - 1`, represented as decreasing `Nat`-fuel recursion, and returns `0` if the candidate search fuel is exhausted.  This example exercises the scalar compiler path without adding new primitives.

Checks run:

- [x] `lake build LeanExe.Examples.Prime`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Prime --entry LeanExe.Examples.Prime.next --out .lake/build/prime-next.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Prime --entry LeanExe.Examples.Prime.next --out .lake/build/prime-next.wat`
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke next .lake/build/prime-next.wasm 0` returned `2`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke next .lake/build/prime-next.wasm 2` returned `3`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke next .lake/build/prime-next.wasm 14` returned `17`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke next .lake/build/prime-next.wasm 1000` returned `1009`.
- [x] `lake env lean --stdin` with the same four `#eval LeanExe.Examples.Prime.next` calls returned `2`, `3`, `17`, and `1009`.

## 2026-05-06: Correct Array UInt64 Semantics

The CoreWasm array layout now stores `Array UInt64` values as pointers to a length header followed by eight-byte cells.  `Array.replicate n 0` writes the length and allocates zero-filled cells.  `Array.get!Internal` and `GetElem?.getElem!` check the index before loading; an out-of-bounds index emits a Wasm trap, matching ordinary Lean execution of `a[i]!`.  `Array.set!` evaluates its arguments, checks the index, allocates a fresh array, copies all cells, updates one cell, and returns the new pointer.  Old aliases keep pointing at the old array.

`LeanExe.Examples.ArraySemantics.aliasCheck` captures the aliasing case that the old in-place lowering got wrong.  The program builds a base array with element `0` equal to `11`, computes `(a.set! 0 22)[0]! * 100 + a[0]!`, and returns `2211`.  The old in-place lowering would have returned `2222`.

Checks run:

- [x] `lake build`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.ArraySemantics --entry LeanExe.Examples.ArraySemantics.aliasCheck --out .lake/build/array-alias.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.ArraySemantics --entry LeanExe.Examples.ArraySemantics.oobGet --out .lake/build/array-oob-get.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.ArraySemantics --entry LeanExe.Examples.ArraySemantics.oobSet --out .lake/build/array-oob-set.wasm`
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke aliasCheck .lake/build/array-alias.wasm` returned `2211`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke oobGet .lake/build/array-oob-get.wasm` trapped with `wasm unreachable`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke oobSet .lake/build/array-oob-set.wasm` trapped with `wasm unreachable`.
- [x] `lake env lean --stdin` with `#eval LeanExe.Examples.ArraySemantics.aliasCheck` returned `2211`.
- [x] The integer-map regression still returned `17`, `1007`, `0`, and `51200` for `query 1`, `query 100`, `query 101`, and `checksum`.

## 2026-05-06: Local Let Bindings

The generic extractor now lowers Lean `.letE` expressions into `LeanExe.IR.Expr.letE` with an explicit local slot.  The slot allocator threads through nested expressions, branches, conditions, call arguments, and the supported `Nat.brecOn` tail-recursion shape.  Recursive update temporaries now start after locals required by extracted loop conditions and recursive arguments, preventing collisions between let-bound locals and loop-update staging slots.

The CoreWasm emitter lowers an IR let by evaluating the bound value, assigning it to the chosen Wasm local, and emitting the body.  At that checkpoint, the implementation accepted let-bound `Bool`, `UInt64`, bounded `Nat`, and `Array UInt64` values.  Product lets were added later.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Let`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Let --entry LeanExe.Examples.Let.aliasLet --out .lake/build/let-alias.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Let --entry LeanExe.Examples.Let.singleArrayUse --out .lake/build/let-single-array.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Let --entry LeanExe.Examples.Let.boolLet --out .lake/build/let-bool.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Let --entry LeanExe.Examples.Let.letCondition --out .lake/build/let-condition.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Let --entry LeanExe.Examples.Let.recArgLetDemo --out .lake/build/let-rec-arg.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Let --entry LeanExe.Examples.Let.branchArray --out .lake/build/let-branch-array.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Let --entry LeanExe.Examples.Let.bumpDemo --out .lake/build/let-bump-demo.wasm`
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke aliasLet .lake/build/let-alias.wasm` returned `2211`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke singleArrayUse .lake/build/let-single-array.wasm` returned `14`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke boolLet .lake/build/let-bool.wasm 3` returned `44`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke boolLet .lake/build/let-bool.wasm 2` returned `55`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke letCondition .lake/build/let-condition.wasm 3` returned `1`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke letCondition .lake/build/let-condition.wasm 2` returned `0`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke recArgLetDemo .lake/build/let-rec-arg.wasm` returned `10`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke branchArray .lake/build/let-branch-array.wasm 0` returned `5`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke branchArray .lake/build/let-branch-array.wasm 1` returned `9`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke bumpDemo .lake/build/let-bump-demo.wasm` returned `2`.
- [x] Lean evaluation for `aliasLet`, `singleArrayUse`, `boolLet 3`, `boolLet 2`, `letCondition 3`, `letCondition 2`, `recArgLetDemo`, `branchArray 0`, `branchArray 1`, and `bumpDemo` returned `2211`, `14`, `44`, `55`, `1`, `0`, `10`, `5`, `9`, and `2`.
- [x] At that checkpoint, `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Let --entry LeanExe.Examples.Let.unsupportedLetPair --out .lake/build/let-unsupported-pair.wasm` failed with `unsupported let-bound type: Prod.{0, 0} UInt64 UInt64`.

## 2026-05-06: Core Correctness Corpus

`LeanExe.Examples.Correctness` collects small checked Lean programs that stress semantic edges in the generic compiler fragment.  At that checkpoint, the accepted cases covered boolean short-circuiting with skipped traps, `UInt64` division and remainder at zero divisors, wraparound arithmetic, nested lexical shadowing, lets in call arguments, array update and read ordering, and lets inside recursive arguments.  The rejected cases covered product lets, nonzero array replication, higher-order arguments, and `IO`.

The corpus found three concrete issues.  CoreWasm condition lowering used Wasm `i32.and` and `i32.or`, which evaluated both operands and therefore trapped for `true || rhs` and `false && rhs` when `rhs` contained an out-of-bounds array access.  CoreWasm `UInt64` division and remainder used Wasm `i64.div_u` and `i64.rem_u` directly, but Lean returns `0` for `x / 0` and `x` for `x % 0`.  The signed LEB128 encoder for `i64.const` emitted invalid Wasm for `UInt64` constants above `Int64.max`; those constants now lower through the signed two’s-complement representation of the same 64-bit pattern.

The corpus also exposed a limitation in the first `Nat.brecOn` tail-recursion extractor.  The old lowering assumed that the loop result was the last carried parameter.  The extractor now parses the generated matcher, extracts the base arm, extracts an optional early-exit value from the successor arm, and emits a result expression that distinguishes fuel exhaustion from early exit.  The successor arm still must either tail-call the recursive handle or use `if cond then exitValue else recursiveCall`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] Lean evaluation for `shortOrSkipsTrap`, `shortAndSkipsTrap`, `divByZero`, `modByZero`, `overflow`, `underflow`, `nestedShadow 3`, `callArgLets 7`, `arrayUpdateRead`, `recLetDemo`, and `recExitDemo` returned `1`, `0`, `0`, `5`, `0`, `18446744073709551615`, `64`, `809`, `110`, `518`, and `314`.
- [x] `node test/core_correctness.js` returned `checked 11 accepted and 4 rejected cases`.
- [x] `node test/fuzz_validate.js .lake/build/validate.wasm 200` returned `checked 206 cases`.
- [x] Wasmtime regressions returned `2211` for array aliasing, `51200` for `IntMap.checksum`, `1009` for `Prime.next 1000`, and `111` for `Collatz.steps 27`.

## 2026-05-06: Internal Product Values

The extractor now represents products as structured extractor values rather than Wasm values.  Product construction, `.1`, `.2`, product-valued local lets, product-valued `if` expressions, nested products, products containing `Array UInt64` pointers, and projections inside recursive-call arguments compile when every field belongs to the first fragment.  Product-valued entry parameters and product-valued entry results remain rejected, because the CoreWasm ABI still exports scalar `i64` values and array pointers only.

Product projection follows Lean’s lazy projection behavior.  `(bad, value).2` and `let pair := (bad, value); pair.2` do not evaluate `bad`, so the extractor keeps products as field expressions and selects the demanded field.  The same work fixed unused scalar lets: `let x := bad; value` no longer forces `bad` when `x` is not referenced by the body.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] Lean evaluation for `productLet`, `nestedProduct`, `productSkipsUnusedField`, `productBranch 0`, `productBranch 1`, `productArrayAlias`, `recProductDemo`, and `unusedScalarLetSkipsTrap` returned `12`, `203`, `7`, `12`, `34`, `2211`, `10`, and `1`.
- [x] `node test/core_correctness.js` returned `checked 19 accepted and 5 rejected cases`.
- [x] `node test/fuzz_validate.js .lake/build/validate.wasm 200` returned `checked 206 cases`.
- [x] Node WebAssembly execution checks returned `2211` for array aliasing, `51200` for `IntMap.checksum`, `1009` for `Prime.next 1000`, and `111` for `Collatz.steps 27`.

## 2026-05-06: Lazy Bindings, Option Values, and Strict Calls

The next correctness pass found a mismatch between Lean evaluation and the eager scalar-let lowering.  Lean returns `7` for `let x := bad; (x, 7).2`, because the projection does not demand the first product field.  The extractor now represents let-bound values as thunks over the checked expression and its de Bruijn environment, forcing the thunk only when the body demands it.

The same issue applies to nonrecursive helper calls.  Lean returns `1` for `ignore bad` when the helper ignores its argument, while Wasm function calls evaluate arguments before entering the callee.  The extractor now inlines nonrecursive project-local helper calls with lazy argument thunks; recursive helpers still compile as Wasm functions when the supported `Nat.brecOn` loop extraction requires that representation.

The extractor now computes demand summaries for project-local helper calls.  Each summary records parameters that may be demanded and parameters that must be demanded when the helper result is demanded.  Strict Wasm calls are rejected when an argument may trap and the callee does not must-demand the corresponding parameter.  `LeanExe.Examples.Correctness.rejectRecursiveIgnoredTrapArg` captures the direct case: Lean evaluates the program to `7`, while the old Wasm lowering trapped before the helper could take its fuel-zero base branch.  `rejectRecursiveIgnoredHiddenTrapArg` captures the indirect case, where the trap is hidden behind a zero-argument project-local declaration.  Recursive summaries are conservative: the fuel parameter is must-demanded, carried parameters are may-demanded, and a later pass should either inline supported loop calls at the call site or compute more precise carried-parameter demand.

`Option` values are now extractor-level tagged values.  `Option.none`, `Option.some`, local `Option` lets, `if` expressions returning `Option`, and matches over `Option UInt64` compile when the final entry result remains a scalar first-fragment value.  `Option` entry parameters and entry results remain rejected because the current Wasm ABI exposes only scalar `i64` values and array pointers.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 29 accepted and 9 rejected cases`.
- [x] Lean evaluation for `letUsedOnlyInUnusedProductField`, `ignoredCallArgSkipsTrap`, `callArgUsedOnlyInUnusedProductField`, `optionSomeMatch`, `optionNoneMatchSkipsSomeArm`, `optionSomeMatchSkipsUnusedPayload`, `optionLet`, `optionBranch 0`, and `optionBranch 1` returned `7`, `1`, `7`, `8`, `5`, `9`, `18`, `11`, and `34`.
- [x] Lean evaluation for `recursiveDemandedFuelGet`, `rejectRecursiveIgnoredTrapArg`, and `rejectRecursiveIgnoredHiddenTrapArg` returned `7`, `7`, and `7`; compilation accepts the demanded-fuel case and rejects the ignored-argument cases.
- [x] `node test/fuzz_validate.js .lake/build/validate.wasm 200` returned `checked 206 cases`.
- [x] Wasmtime 44.0.0 from `build/tools/wasmtime/current/wasmtime` returned `11` and `34` for `optionBranch 0` and `optionBranch 1`.
- [x] Wasmtime regressions returned `111` for `Collatz.steps 27`, `51200` for `IntMap.checksum`, `1009` for `Prime.next 1000`, and `2211` for array aliasing.

## 2026-05-06: Generic Read-Only ByteArray Input

The generic compiler now accepts a `ByteArray` parameter as a structured extractor value backed by two Wasm ABI slots: pointer and length.  `ByteArray.size` reads the length slot, and `ByteArray.get!` lowers to a bounds check followed by `i32.load8_u` and zero extension to the scalar `i64` representation.  Function calls and the supported `Nat.brecOn` loop shape flatten `ByteArray` values when crossing a strict Wasm call boundary, while Lean source functions still see one `ByteArray` parameter.

`LeanExe.Examples.AsciiDigits.validateGeneric : ByteArray -> Bool` is the first byte-buffer program compiled through `lean-wasm compile`.  It keeps the original proof-oriented `validate` declaration unchanged and uses a fuel-bounded loop over the input length plus one, so the empty input returns `true` and the terminal length check does not read past the end of the buffer.  The generic validator is still read-only: the host writes bytes into exported memory and calls the entry function as `validateGeneric(ptr, len)`.

Wasmtime was no longer present under `/tmp`, so this pass downloaded the official Wasmtime 36.0.9 `aarch64-linux` release into `.lake/build/tools`.  That release is marked latest on the upstream GitHub releases page as of 2026-05-06.  The Wasmtime check uses a generated WAST file with active data segments because the generic module exports memory but does not yet export `alloc` or a host helper for writing byte inputs through the CLI.

Checks run:

- [x] `lake build`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.AsciiDigits --entry LeanExe.Examples.AsciiDigits.validateGeneric --out .lake/build/ascii-generic.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.AsciiDigits --entry LeanExe.Examples.AsciiDigits.validateGeneric --out .lake/build/ascii-generic.wat`
- [x] `node test/fuzz_validate.js .lake/build/ascii-generic.wasm 200` returned `checked 206 cases`.
- [x] `.lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --version` returned `wasmtime 36.0.9 (c59270b18 2026-05-05)`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime wast .lake/build/ascii-generic.wast` accepted generated assertions for empty input, all-digit input, invalid input, and a valid prefix.

## 2026-05-06: Generic Comparison Primitives

The generic IR now has unsigned `<` and `<=` conditions.  The extractor recognizes Lean conditions elaborated as `LT.lt` and `LE.le`, including conditions over bounded `Nat` and `UInt64` values, and CoreWasm lowers them to `i64.lt_u` and `i64.le_u`.  This keeps the current fixed-width representation explicit: accepted runtime `Nat` comparisons are comparisons over the bounded `i64` values already admitted into the fragment, not arbitrary-precision `Nat` execution.

`LeanExe.Examples.AsciiDigits.isAsciiDigitNat` now uses the source-level range check `48 <= n` and `n <= 57` instead of ten equality tests.  `LeanExe.Examples.Correctness` adds separate `Nat` and `UInt64` comparison cases for values below, at, and above the branch boundary.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 35 accepted and 9 rejected cases`.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.AsciiDigits --entry LeanExe.Examples.AsciiDigits.validateGeneric --out .lake/build/ascii-generic.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.AsciiDigits --entry LeanExe.Examples.AsciiDigits.validateGeneric --out .lake/build/ascii-generic.wat`
- [x] `node test/fuzz_validate.js .lake/build/ascii-generic.wasm 200` returned `checked 206 cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime wast .lake/build/ascii-generic.wast` accepted generated assertions for empty input, all-digit input, invalid input, and a valid prefix.

## 2026-05-06: Generic Array Size

The generic IR now has `Array.size` as a scalar expression.  CoreWasm lowers it to an `i64.load` from the array header, the same header already used by bounds checks and copy-on-write updates.  This lets source programs inspect array lengths without adding a new layout rule.

`LeanExe.Examples.Correctness.arraySizeAfterSet` checks that `Array.set!` preserves the length header while returning a fresh array pointer.  The function returns `Nat`, which remains represented as an `i64` in the bounded fragment.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 36 accepted and 9 rejected cases`.

## 2026-05-06: Generic Array Push

The generic compiler now lowers `Array.push` for `Array UInt64`.  CoreWasm evaluates the source array and pushed value, loads the old length, allocates a new array with length `oldLen + 1`, copies existing cells, writes the pushed value at the old length, and returns the new pointer.  This matches the conservative copy-on-write discipline already used by `Array.set!`, so old aliases keep the old length and old cells.

`LeanExe.Examples.Correctness.arrayPushRead` checks the pushed length, old-array length, preserved first cell, and new last cell.  The direct Wasmtime check exercises the emitted binary for that example rather than only Node’s WebAssembly runtime.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 37 accepted and 9 rejected cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayPushRead .lake/build/core-correctness/arrayPushRead.wasm` returned `507`.

## 2026-05-06: Generic Allocator Exports

Generic CoreWasm modules now export `alloc(len : i64) -> i64` and `reset()`.  The heap global starts at byte offset `4096`, matching the original validator module, and every generic array allocation uses the same heap global.  A host that needs to pass a `ByteArray` can now call `reset`, call `alloc`, write bytes at the returned pointer, and pass `(ptr, len)` to the entry function without guessing a memory address that might overlap later compiled allocations.

The generic function indices remain stable because the runtime functions are appended after user functions.  User calls still refer to the same indices, and the runtime exports use indices `funcs.size` and `funcs.size + 1`.  The validator fuzz harness now uses the generic allocator when `validateGeneric`, `alloc`, and `reset` are present, while retaining support for the older hand-written validator ABI.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 37 accepted and 9 rejected cases`.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.AsciiDigits --entry LeanExe.Examples.AsciiDigits.validateGeneric --out .lake/build/ascii-generic.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.AsciiDigits --entry LeanExe.Examples.AsciiDigits.validateGeneric --out .lake/build/ascii-generic.wat`
- [x] `node test/fuzz_validate.js .lake/build/ascii-generic.wasm 200` returned `checked 206 cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke alloc .lake/build/ascii-generic.wasm 4` returned `4096`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime wast .lake/build/ascii-generic.wast` accepted allocator and validator assertions.

## 2026-05-06: Nonzero Array Replication

`Array.replicate` now supports nonzero `UInt64` fill values.  CoreWasm still uses the zero-allocation path for literal zero fills, but nonzero fills evaluate the length and value, allocate the array header and cells, and run a fill loop that writes the value into each cell.  The value is evaluated once before the fill loop, matching the source-level call argument.

`LeanExe.Examples.Correctness.nonzeroReplicateRead` checks the new path by reading two initialized cells and checking the resulting size.  The previous rejection case for nonzero replication was removed from the correctness harness because the feature now compiles.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 38 accepted and 8 rejected cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke nonzeroReplicateRead .lake/build/core-correctness/nonzeroReplicateRead.wasm` returned `77`.

## 2026-05-06: Generic Array Pop

The generic compiler now lowers `Array.pop` for `Array UInt64`.  Empty arrays return the original pointer, matching Lean’s empty-pop behavior.  Nonempty arrays allocate a fresh array with length `oldLen - 1`, copy the retained prefix, and return the new pointer, preserving the copy-on-write rule used by `set!` and `push`.

`LeanExe.Examples.Correctness.arrayPopRead` checks pop after push, the old array length, the popped array length, empty-pop behavior, and retained cells.  The Wasmtime check runs the emitted binary for that example.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 39 accepted and 8 rejected cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayPopRead .lake/build/core-correctness/arrayPopRead.wasm` returned `44`.

## 2026-05-06: UInt64 Bitwise Or and Xor

The scalar IR now supports `UInt64.lor` and `UInt64.xor`, complementing the existing `UInt64.land` lowering.  CoreWasm emits `i64.or` and `i64.xor`; these operations preserve the current fixed-width `UInt64` representation without adding new ABI rules.

`LeanExe.Examples.Correctness.bitwiseOrXor` checks the new operations together with `land`, and Wasmtime runs the emitted binary for that case.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 40 accepted and 8 rejected cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke bitwiseOrXor .lake/build/core-correctness/bitwiseOrXor.wasm` returned `6`.

## 2026-05-06: UInt64 Shifts

The scalar IR now supports `UInt64.shiftLeft` and `UInt64.shiftRight`.  Local Lean checks showed that Lean masks the shift count modulo 64 for `UInt64`, matching Wasm `i64.shl` and `i64.shr_u`; for example, shifting by `65` behaves like shifting by `1`.

`LeanExe.Examples.Correctness.shiftMasking` checks both left and right shifts with a count of `65`, and Wasmtime runs the emitted binary for that case.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 41 accepted and 8 rejected cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke shiftMasking .lake/build/core-correctness/shiftMasking.wasm` returned `42`.

## 2026-05-06: Greater-Than Comparisons

The extractor now recognizes Lean conditions elaborated as `GT.gt` and `GE.ge`.  They lower by reversing the operands of the existing unsigned `<` and `<=` IR conditions, so no new Wasm condition form was needed.

`LeanExe.Examples.Correctness.greaterComparisons` checks `>` and `>=` across the below, boundary, and above cases.  Wasmtime runs the emitted binary for the above case.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 44 accepted and 8 rejected cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke greaterComparisons .lake/build/core-correctness/greaterComparisons.wasm 6` returned `30`.

## 2026-05-06: Reserved Runtime Export Names

Generic modules now reject entry points whose short export name would collide with runtime exports.  The reserved names are `memory`, `alloc`, and `reset`.  Without this check, a source function named `alloc` could compile to a module with duplicate exports after the generic allocator was added.

`LeanExe.Examples.Correctness.alloc` is a valid scalar Lean definition, but compiling it as an entry now fails with `entry export name is reserved by the runtime ABI: alloc`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 44 accepted and 9 rejected cases`.

## 2026-05-06: ByteArray Input with Later Allocation

`LeanExe.Examples.ByteArrayPrograms.firstBytePlusArray` exercises a mixed ByteArray-and-array program.  The host passes a `ByteArray` through the generic `(ptr, len)` ABI, and the compiled function then allocates an `Array UInt64` before reading the input byte.  This catches heap-overlap regressions in the generic allocator: input allocated by the host must remain valid after compiled code allocates.

`test/bytearray_alloc.js` builds the example module, compiles it through `lean-wasm compile`, allocates host input through the module’s exported allocator, writes the bytes into memory, and calls the compiled entry.  The Wasmtime WAST check covers the same scenario with an active data segment at the allocator’s first returned pointer.

Checks run:

- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.ByteArrayPrograms --entry LeanExe.Examples.ByteArrayPrograms.firstBytePlusArray --out .lake/build/bytearray-first-plus-array.wasm`
- [x] `node test/bytearray_alloc.js` returned `checked 3 bytearray allocation cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.ByteArrayPrograms --entry LeanExe.Examples.ByteArrayPrograms.firstBytePlusArray --out .lake/build/bytearray-first-plus-array.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime wast .lake/build/bytearray-first-plus-array.wast` accepted the allocator-plus-entry assertion.

## 2026-05-06: Nat Subtraction Semantics

The extractor previously lowered every `HSub.hSub` application to wrapping `i64.sub`.  That was correct for `UInt64`, but wrong for `Nat`: Lean’s `Nat` subtraction saturates at zero.  The extractor now inspects the primitive result type and emits a dedicated bounded-`Nat` subtraction operation for `Nat` results.  CoreWasm evaluates both operands once, returns `0` when `left < right`, and otherwise emits `left - right`.

`LeanExe.Examples.Correctness.natSubSaturates` checks the underflow case, and `natSubNormal` checks ordinary subtraction.  `UInt64` subtraction still uses wrapping subtraction, so the existing `underflow` test continues to return `18446744073709551615`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 46 accepted and 9 rejected cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke natSubSaturates .lake/build/core-correctness/natSubSaturates.wasm` returned `0`.

## 2026-05-06: Bounded Nat Literal Rejection

Runtime `Nat` literals now receive an explicit bound check during extraction.  Literals below `2^64` continue to lower to the scalar `i64` representation; larger literals are rejected with `Nat literal exceeds bounded runtime representation`.  This avoids silently compiling an arbitrary-precision Lean `Nat` literal to its low 64 bits.

`LeanExe.Examples.Correctness.rejectHugeNatLiteral` covers the first out-of-range value, `18446744073709551616`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 46 accepted and 10 rejected cases`.

## 2026-05-06: Checked Nat Addition and Multiplication

The extractor now emits distinct IR operations for `Nat` addition and multiplication instead of reusing wrapping `UInt64` operations.  `Nat` addition evaluates both operands once, computes the `i64` sum, and traps if the unsigned result wrapped below the left operand.  `Nat` multiplication traps when `left > UInt64.max / right`, with a separate zero case.  These traps mark values outside the current bounded `Nat` subset rather than returning a truncated result.

The correctness harness now has a third category for programs that compile but must trap at runtime.  `natAddOverflow` and `natMulOverflow` cover the first overflowing values.  Normal `Nat` addition and multiplication still compile and return their expected bounded results.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 48 accepted, 10 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke natAddOverflow .lake/build/core-correctness/natAddOverflow.wasm` trapped with `wasm unreachable`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke natMulOverflow .lake/build/core-correctness/natMulOverflow.wasm` trapped with `wasm unreachable`.

## 2026-05-06: UInt64.ofNat

The extractor now recognizes `UInt64.ofNat`.  For a literal argument, it lowers directly to a `UInt64` constant, preserving Lean’s modulo-`2^64` behavior for large literals.  For a runtime `Nat` expression, it lowers the bounded scalar value directly; values outside the bounded `Nat` representation cannot arise without a prior trap.

`LeanExe.Examples.Correctness.uint64OfNatValue` checks a runtime bounded conversion, and `uint64OfHugeNat` checks that a literal equal to `2^64` converts to `0` rather than receiving the bounded-`Nat` literal rejection.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 50 accepted, 10 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke uint64OfHugeNat .lake/build/core-correctness/uint64OfHugeNat.wasm` returned `0`.

## 2026-05-06: ByteArray Result Rejection

The function type checker now distinguishes parameter ABI support from result ABI support.  A `ByteArray` parameter is allowed and flattens to `(ptr, len)`, but a `ByteArray` result is rejected because generic CoreWasm functions still return one `i64`.  This moves byte-array result rejection to the function type boundary instead of letting extraction fail later when a structured value is used as a scalar.

`LeanExe.Examples.Correctness.rejectByteArrayReturn` covers the case.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 50 accepted, 11 rejected, and 2 trapped cases`.

## 2026-05-06: Internal UInt8 Values

`ByteArray.get!` returns `UInt8`, so byte-oriented programs need to compare byte reads with `UInt8` literals without converting through `Nat`.  At this checkpoint, the extractor admitted `UInt8` as a local scalar type while keeping `UInt8` out of the exported function ABI.  `OfNat UInt8` and `UInt8.ofNat` lower modulo `256`, matching Lean evaluation for values such as `(300 : UInt8).toNat = 44`.

`LeanExe.Examples.ByteArrayPrograms.firstByteIsStar` checks a `ByteArray.get!` result against `(42 : UInt8)`.  `LeanExe.Examples.Correctness.wrappedUInt8Literal` covers literal wrapping, and `uint8OfNatValue` covers runtime bounded-`Nat` conversion through `UInt8.ofNat`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/core_correctness.js` returned `checked 52 accepted, 11 rejected, and 2 trapped cases`.
- [x] `node test/bytearray_alloc.js` returned `checked 6 bytearray allocation cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke wrappedUInt8Literal .lake/build/core-correctness/wrappedUInt8Literal.wasm` returned `44`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke uint8OfNatValue .lake/build/core-correctness/uint8OfNatValue.wasm 298` returned `43`.

## 2026-05-06: Internal UInt8 Helper Signatures

The compiler now separates exported entry ABI support from project-local helper support.  Exported entries still rejected `UInt8` parameters and results at this checkpoint, because the public ABI had not assigned byte-sized scalar slots.  Internal helpers may use `UInt8` parameters and results, and the lowering represents those values as scalar `i64` slots constrained by the operations that produce them.  The later public `UInt8` and `UInt32` ABI entry supersedes this boundary.

`LeanExe.Examples.ByteArrayPrograms.nextByte` takes and returns `UInt8`.  `firstByteNextIsZero` calls it on a `ByteArray.get!` result and checks the modulo-256 wrap from `255` to `0`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/core_correctness.js` returned `checked 52 accepted, 13 rejected, and 2 trapped cases`.
- [x] `node test/bytearray_alloc.js` returned `checked 9 bytearray allocation cases`.

## 2026-05-06: UInt8 Arithmetic Wrapping

Accepting internal `UInt8` values made the previous generic lowering of `HAdd`, `HSub`, and `HMul` too broad.  Those primitives reused the `UInt64` operations unless the result type was `Nat`, which would compile `(255 : UInt8) + 1` as `256` instead of `0`.  The extractor now inspects the primitive result type and masks `UInt8` addition, subtraction, and multiplication to eight bits.

`UInt8` division and remainder already match Lean under the existing checked unsigned lowering for zero divisors: `x / 0` returns `0`, and `x % 0` returns `x`.  `LeanExe.Examples.Correctness.uint8AddWrap`, `uint8SubWrap`, `uint8MulWrap`, and `uint8DivModZero` cover these cases.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 56 accepted, 13 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke uint8AddWrap .lake/build/core-correctness/uint8AddWrap.wasm` returned `0`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke uint8SubWrap .lake/build/core-correctness/uint8SubWrap.wasm` returned `255`.

## 2026-05-06: Bool Pattern Matching

The generic extractor now lowers `Bool.casesOn` and generated `match_*` declarations whose scrutinee type is `Bool`.  Earlier matcher recognition treated every generated matcher as an `Option` matcher, which caused Bool matches to fail while trying to read scalar values as `Option` tags.  The extractor now classifies generated matchers by the scrutinee type in the checked matcher declaration before choosing the Bool or Option lowering.

Bool matches use the existing conditional IR and preserve branch laziness, so a skipped match arm may contain a partial expression such as an out-of-bounds array access.  Structured match results use the same extractor-level `valueIte` path as structured `if` expressions.

`LeanExe.Examples.Correctness.boolMatchScalar`, `boolMatchSkipsTrap`, `boolMatchCondition`, and `boolMatchProduct` cover scalar results, branch laziness, boolean-valued matches used as conditions, and product-valued match results.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 63 accepted, 13 rejected, and 2 trapped cases`.
- [x] `node test/bytearray_alloc.js` returned `checked 9 bytearray allocation cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke boolMatchSkipsTrap .lake/build/core-correctness/boolMatchSkipsTrap.wasm` returned `7`.

## 2026-05-06: Decidable Comparison Booleans

Lean programs often use `decide` to turn a decidable proposition into a `Bool`.  The extractor now recognizes `Decidable.decide` when the proposition is already in the supported condition fragment, such as bounded `Nat` or `UInt64` comparisons.  Unsupported propositions still fail through the existing condition extractor rather than receiving a broad or guessed lowering.

`LeanExe.Examples.Correctness.decideNatLt` covers a `Nat` comparison used as an `if` condition through `decide`, and `decideUInt64Ge` covers a `Bool` result produced directly from a decided `UInt64` comparison.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 67 accepted, 13 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke decideUInt64Ge .lake/build/core-correctness/decideUInt64Ge.wasm 3` returned `1`.

## 2026-05-06: Scalar Propositional Equality

The condition extractor now supports `Eq` propositions over admitted scalar runtime types: `Bool`, `UInt8`, `UInt64`, and bounded `Nat`.  This admits ordinary Lean forms such as `if x = 3 then ...` and `decide (x = 3)` without requiring source code to use `==`.  Equality over structured values remains unsupported until those values have an explicit equality lowering.

`LeanExe.Examples.Correctness.propEqNat` covers direct propositional equality in an `if`, `decideEqUInt64` covers equality through `Decidable.decide`, and `propEqBoolSkipsTrap` checks that equality against `true` still preserves short-circuit evaluation inside the boolean expression.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 72 accepted, 13 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke propEqBoolSkipsTrap .lake/build/core-correctness/propEqBoolSkipsTrap.wasm` returned `1`.

## 2026-05-06: Proposition Connectives

The condition extractor now supports proposition-level `And`, `Or`, `Not`, `True`, and `False` when their subconditions are already in the supported fragment.  This admits source forms such as `if x > 1 ∧ x < 5 then ...` and `decide (x < 2 ∨ x > 5)`.  The lowering uses the same short-circuiting condition IR as boolean `&&` and `||`.

`LeanExe.Examples.Correctness.propAndNat`, `propOrNat`, and `propNotNat` cover compound `Nat` propositions.  `propOrSkipsTrap` and `propAndSkipsTrap` check that proposition connectives do not evaluate skipped branches containing partial array reads.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 81 accepted, 13 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke propOrSkipsTrap .lake/build/core-correctness/propOrSkipsTrap.wasm` returned `1`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke propAndSkipsTrap .lake/build/core-correctness/propAndSkipsTrap.wasm` returned `0`.

## 2026-05-06: Scalar Min and Max

The extractor now lowers `Min.min` and `Max.max` for bounded `Nat`, `UInt8`, and `UInt64`.  The lowering uses unsigned scalar comparisons over the existing runtime representation.  This keeps `Nat.min` and `Nat.max` inside the bounded fragment and gives byte and word-sized code the usual scalar selection operations.

`LeanExe.Examples.Correctness.natMinMax`, `u64MinMax`, and `u8MinMax` cover the supported types.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 86 accepted, 13 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke u8MinMax .lake/build/core-correctness/u8MinMax.wasm` returned `280`.

## 2026-05-06: Bitwise Operator Notation

The extractor now lowers `HAnd.hAnd`, `HOr.hOr`, and `HXor.hXor` for `UInt64` and internal `UInt8` values.  Lean elaborates the `&&&`, `|||`, and `^^^` notations through those typeclass operations, while earlier examples used the direct `UInt64.land`, `UInt64.lor`, and `UInt64.xor` functions.

`LeanExe.Examples.Correctness.bitwiseNotation` covers the notation path and returns the same result as the direct-call `bitwiseOrXor` example.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 87 accepted, 13 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke bitwiseNotation .lake/build/core-correctness/bitwiseNotation.wasm` returned `6`.

## 2026-05-06: Shift Operator Notation

The extractor now lowers `HShiftLeft.hShiftLeft` and `HShiftRight.hShiftRight` for `UInt64`.  Lean elaborates `<<<` and `>>>` through those typeclass operations, while existing coverage used direct `UInt64.shiftLeft` and `UInt64.shiftRight` calls.

`LeanExe.Examples.Correctness.shiftNotation` covers the notation path and keeps the existing shift-count masking expectation.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 88 accepted, 13 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke shiftNotation .lake/build/core-correctness/shiftNotation.wasm` returned `42`.

## 2026-05-06: Bitwise Complement

The extractor now lowers `Complement.complement` for `UInt64` and internal `UInt8` values.  `UInt64` complement lowers to xor with `2^64 - 1`; `UInt8` complement lowers to xor with `255`.  The primitive application code also now isolates inline calls, emitted calls, unary primitives, and binary primitives in separate helper functions, which keeps additional primitive cases out of the main expression matcher.

`LeanExe.Examples.Correctness.complementNotation` covers `~~~` on `UInt64`, and `u8Complement` covers the internal `UInt8` path.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 90 accepted, 13 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke complementNotation .lake/build/core-correctness/complementNotation.wasm` returned `255`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke u8Complement .lake/build/core-correctness/u8Complement.wasm` returned `255`.

## 2026-05-06: Byte UInt8 Bitwise Coverage

`firstByteLowNibble` exercises `UInt8` bitwise notation on a value returned by `ByteArray.get!`.  This covers the path real byte-oriented code uses: host input enters memory, `ByteArray.get!` produces an internal `UInt8`, and `&&&` lowers through `HAnd.hAnd` without converting through `Nat`.

Checks run:

- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 12 bytearray allocation cases`.

## 2026-05-06: ByteArray.isEmpty

The extractor now lowers `ByteArray.isEmpty` to a length comparison against zero.  This is the same value already available through the `ByteArray` parameter ABI, so it adds a source-level convenience without changing the memory representation.

`LeanExe.Examples.ByteArrayPrograms.emptyViaIsEmpty` covers the new primitive in the byte-array allocation harness.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 14 bytearray allocation cases`.

## 2026-05-06: ByteArray Bang Indexing

`input[i]!` for `ByteArray` elaborates through `GetElem?.getElem!`, not `ByteArray.get!`.  The extractor now distinguishes the receiver type for `GetElem?.getElem!` and lowers `ByteArray` receivers to the byte-array bounds check and `i32.load8_u` path.  `Array UInt64` receivers continue to use the existing array load path.

`LeanExe.Examples.ByteArrayPrograms.firstByteBangIndex` covers empty input and two byte values through the byte-array allocation harness.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 17 bytearray allocation cases`.
- [x] `node test/core_correctness.js` returned `checked 95 accepted, 13 rejected, and 3 trapped cases`.

## 2026-05-06: Mixed ByteArray and Scalar ABI

`LeanExe.Examples.ByteArrayPrograms.byteAtOrZero` takes a `ByteArray` followed by a bounded `Nat` index.  This checks that the flattened byte-array ABI slots `(ptr, len)` compose with later scalar parameters in the exported Wasm signature.  The host calls the compiled function as `(ptr, len, index)`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 20 bytearray allocation cases`.

## 2026-05-06: Array.isEmpty

The extractor now lowers `Array.isEmpty` for `Array UInt64` by reading the array header length and comparing it with zero.  This matches the existing memory layout and avoids requiring source programs to write `a.size == 0`.

`LeanExe.Examples.Correctness.arrayIsEmptyValues` checks both empty and non-empty arrays.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 91 accepted, 13 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayIsEmptyValues .lake/build/core-correctness/arrayIsEmptyValues.wasm` returned `1`.

## 2026-05-06: Array.back!

The extractor now lowers `Array.back!` for `Array UInt64`.  It evaluates the array expression once, binds the array pointer in a local, computes `size - 1`, and reuses the existing bounds-checked array load.  Empty arrays therefore trap through the same `unreachable` path as an out-of-bounds indexed read.

`LeanExe.Examples.Correctness.arrayBackRead` covers the non-empty case.  `arrayBackEmptyTrap` compiles but must trap at runtime.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 92 accepted, 13 rejected, and 3 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayBackRead .lake/build/core-correctness/arrayBackRead.wasm` returned `9`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayBackEmptyTrap .lake/build/core-correctness/arrayBackEmptyTrap.wasm` trapped with `wasm unreachable`.

## 2026-05-06: Array.getD

The extractor now lowers `Array.getD` for `Array UInt64`.  It binds the array pointer and index once, checks the index against the header length, and returns either the bounds-checked load or the default expression.  The default expression stays in the else branch, so an in-bounds read does not evaluate a default that would trap.

`LeanExe.Examples.Correctness.arrayGetDRead` covers in-bounds and out-of-bounds reads.  `arrayGetDSkipsDefaultTrap` checks default-branch laziness.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 95 accepted, 13 rejected, and 3 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayGetDRead .lake/build/core-correctness/arrayGetDRead.wasm 2` returned `99`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayGetDSkipsDefaultTrap .lake/build/core-correctness/arrayGetDSkipsDefaultTrap.wasm` returned `5`.

## 2026-05-06: Combined Correctness Runner

`test/run_all.js` runs the current local correctness suite: `lake build`, `test/core_correctness.js`, `test/bytearray_alloc.js`, and `test/fuzz_validate.js`.  The fuzz case count defaults to `50` and can be changed through `LEANEXE_FUZZ_CASES`.  The runner uses `LEAN_WASM_EXE` when set, matching the existing harnesses.

Checks run:

- [x] `node test/run_all.js` returned `checked 95 accepted, 13 rejected, and 3 trapped cases`, `checked 14 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Scalar Then ByteArray ABI

`LeanExe.Examples.ByteArrayPrograms.prefixPlusFirstByte` takes a scalar `UInt64` before a `ByteArray`.  This checks the other mixed-parameter order for the flattened byte-array ABI: the exported Wasm function receives `(prefix, ptr, len)`.  The prior byte-array harness covered `(ptr, len, scalar)`, so the test suite now exercises both sides of the source-order rule.

Checks run:

- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 23 bytearray allocation cases`.
- [x] `node test/run_all.js` returned `checked 95 accepted, 13 rejected, and 3 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: UInt8 Shifts

The extractor now lowers `UInt8` shift notation and the direct `UInt8.shiftLeft` and `UInt8.shiftRight` functions.  Lean’s `UInt8` shift semantics mask the shift count modulo eight.  Left shifts also wrap the result to eight bits.  The lowering implements that rule with an explicit `count &&& 7` expression and the existing `UInt8` result mask.

`LeanExe.Examples.Correctness.uint8ShiftNotation` covers `<<<` and `>>>` notation.  `uint8DirectShift` covers the named functions, including an overflowing left shift and a right shift whose count equals eight.  Both examples return `Nat` values so the current public ABI remains unchanged.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 97 accepted, 13 rejected, and 3 trapped cases`.
- [x] `node test/run_all.js` returned `checked 97 accepted, 13 rejected, and 3 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array.append

The IR now has an `arrayAppend` expression for `Array UInt64`.  The extractor lowers `Array.append` by evaluating both array arguments once and passing their pointers to that IR expression.  CoreWasm allocates a fresh array, stores the combined length, copies the left cells, and then copies the right cells at an offset equal to the left length.

This implementation follows the same conservative copy-on-write discipline as `Array.set!`, `Array.push`, and nonempty `Array.pop`.  Old aliases keep observing the old arrays.  The WAT printer now has the same append lowering as the binary emitter, and the Wasmtime WAT check covers the generated text path.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 99 accepted, 13 rejected, and 3 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayAppendRead --out .lake/build/core-correctness/arrayAppendRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayAppendRead .lake/build/core-correctness/arrayAppendRead.wat` returned `11223344`.
- [x] `node test/run_all.js` returned `checked 99 accepted, 13 rejected, and 3 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Option.getD

The extractor now lowers `Option.getD` for first-fragment payloads.  It reuses the existing extractor-level tag and payload representation, returning the default value when the tag is zero and the payload otherwise.  The default expression remains inside the `none` branch of the emitted value, so a default that would trap is skipped when the option is `some`.

`LeanExe.Examples.Correctness.optionGetDNone` covers the `none` branch.  `optionGetDSomeSkipsDefaultTrap` checks default laziness with an empty-array `back!` expression.  `optionGetDProduct` checks that structured product payloads pass through the same lowering before projection.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 102 accepted, 13 rejected, and 3 trapped cases`.
- [x] `node test/run_all.js` returned `checked 102 accepted, 13 rejected, and 3 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Option Tag Tests

The extractor now lowers `Option.isSome` and `Option.isNone`.  Both operations inspect only the extractor-level tag and return a scalar `Bool`.  The payload expression is left unused, so a `some` payload that would trap is not evaluated by a tag test.

`LeanExe.Examples.Correctness.optionIsSomeSkipsPayloadTrap` checks that payload laziness.  `optionIsNoneValues` covers both `none` and `some` values in a boolean condition.  These cases keep `Option` inside the existing internal structured-value representation.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 104 accepted, 13 rejected, and 3 trapped cases`.
- [x] `node test/run_all.js` returned `checked 104 accepted, 13 rejected, and 3 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Option.elim

The extractor now lowers `Option.elim` for first-fragment result values.  The lowering extracts the option tag and payload, then emits the default arm for `none` and the function arm for `some`.  Both arms remain branch-local in the emitted value, so the default expression is skipped for `some` and the function body is skipped for `none`.

`LeanExe.Examples.Correctness.optionElimSomeSkipsDefaultTrap` checks the skipped-default case.  `optionElimNoneSkipsSomeArmTrap` checks the skipped-function case.  `optionElimProduct` checks a product result, which exercises the structured-value branch path rather than only scalar extraction.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 107 accepted, 13 rejected, and 3 trapped cases`.
- [x] `node test/run_all.js` returned `checked 107 accepted, 13 rejected, and 3 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Option.map

The extractor now lowers `Option.map` when the mapping function is a one-argument lambda and the result type remains inside the first fragment.  The result keeps the original option tag.  The mapped payload is emitted only for the `some` branch, while the `none` branch uses the default payload for the mapped result type.

`LeanExe.Examples.Correctness.optionMapSome` covers a scalar mapped value.  `optionMapNoneSkipsFunctionTrap` checks that the mapping function is not evaluated for `none`.  `optionMapProduct` checks a structured product result inside an `Option`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 110 accepted, 13 rejected, and 3 trapped cases`.
- [x] `node test/run_all.js` returned `checked 110 accepted, 13 rejected, and 3 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Option.bind

The extractor now lowers `Option.bind` when the bind function is a one-argument lambda returning a supported `Option` value.  If the input option is `none`, the result tag is `none` and the bind function body is not emitted on the executed path.  If the input option is `some`, the result takes the tag and payload produced by the bind function.

`LeanExe.Examples.Correctness.optionBindSome` covers the ordinary `some` case.  `optionBindNoneSkipsFunctionTrap` checks that the bind function is skipped for `none`.  `optionBindFunctionNone` and `optionBindProduct` cover a function that returns `none` and a function that returns an `Option` carrying a product.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 114 accepted, 13 rejected, and 3 trapped cases`.
- [x] `node test/run_all.js` returned `checked 114 accepted, 13 rejected, and 3 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array.extract

The IR now has an `arrayExtract` expression for `Array UInt64`.  The extractor lowers `Array.extract` by evaluating the array, start index, and stop index once.  CoreWasm clamps stop to the source length, computes a zero result length when the effective stop is not greater than start, allocates a fresh array, and copies the selected cells from `start + i` into result cell `i`.

`LeanExe.Examples.Correctness.arrayExtractRead` covers an ordinary interior slice.  `arrayExtractClamps` covers stop clamping, start past the end, and stop before start.  The WAT path is checked with Wasmtime for the clamping case because this feature adds a new text-emitter branch as well as a binary-emitter branch.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 116 accepted, 13 rejected, and 3 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayExtractClamps --out .lake/build/core-correctness/arrayExtractClamps.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayExtractClamps .lake/build/core-correctness/arrayExtractClamps.wat` returned `340`.
- [x] `node test/run_all.js` returned `checked 116 accepted, 13 rejected, and 3 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Nat.succ and Nat.pred

The extractor now lowers direct `Nat.succ` and `Nat.pred` applications.  `Nat.succ` uses the existing checked bounded-`Nat` addition operation with an increment of one, so it traps when the result would exceed the current `i64` representation.  `Nat.pred` uses the existing bounded-`Nat` subtraction operation with a decrement of one, so predecessor at zero returns zero.

`LeanExe.Examples.Correctness.natSuccPred` covers normal successor and predecessor behavior at `5` and the predecessor-at-zero case.  `natSuccOverflow` compiles and traps at runtime, matching the bounded-`Nat` overflow policy used by addition.  This change adds source coverage for code that uses the named `Nat` operations instead of arithmetic notation.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 118 accepted, 13 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 118 accepted, 13 rejected, and 4 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Fixed-Width Scalar Conversions

The extractor now lowers `Nat.toUInt64`, `UInt64.toUInt8`, and `UInt8.toUInt64`.  `Nat.toUInt64` follows the same rule as `UInt64.ofNat`: bounded runtime `Nat` values pass through unchanged, and direct literals lower modulo `2^64` instead of going through bounded-`Nat` literal rejection.  `UInt64.toUInt8` masks to eight bits, while `UInt8.toUInt64` preserves the current scalar representation.

`LeanExe.Examples.Correctness.natToUInt64Value` covers a runtime bounded `Nat` conversion, and `natToUInt64Huge` covers the direct large-literal case.  `uint64ToUInt8Wrap` checks byte masking from `300` to `44`.  `uint8ToUInt64Value` checks widening from `UInt8` before `UInt64` arithmetic.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 122 accepted, 13 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 122 accepted, 13 rejected, and 4 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array Literals

The extractor now lowers `List.toArray` when its argument is a literal `List UInt64`.  This accepts Lean array literal syntax such as `#[]` and `#[10, 20, 30]` without adding general list support.  The lowering allocates an array of the literal length, then uses the existing copy-on-write `arraySet` expression to populate each literal element in source order.

`LeanExe.Examples.Correctness.arrayLiteralRead` covers a nonempty literal.  `arrayEmptyLiteral` covers the empty literal.  The implementation rejects nonliteral lists and non-`UInt64` item types rather than inferring behavior for general `List.toArray`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 124 accepted, 13 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 124 accepted, 13 rejected, and 4 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Internal UInt32

The extractor now admits `UInt32` as an internal scalar type.  It keeps the public ABI unchanged: exported `UInt32` parameters and results are still rejected.  Local values and helper signatures can use `UInt32`, represented as an `i64` whose producing operations constrain the value to `0..2^32-1`.

The lowering follows Lean’s fixed-width behavior.  `UInt32` literals and `UInt32.ofNat` lower modulo `2^32`, `UInt64.toUInt32` masks to 32 bits, and `UInt32.toNat` and `UInt32.toUInt64` preserve the constrained representation.  Addition, subtraction, multiplication, bitwise operations, complement, shifts, `min`, and `max` now have `UInt32` cases.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 132 accepted, 15 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 132 accepted, 15 rejected, and 4 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: UInt8 and UInt32 Conversions

The extractor now lowers `UInt8.toUInt32` and `UInt32.toUInt8`.  Widening from `UInt8` to `UInt32` preserves the constrained scalar representation.  Narrowing from `UInt32` to `UInt8` masks to eight bits, matching Lean’s fixed-width conversion behavior.

`LeanExe.Examples.Correctness.uint8ToUInt32Value` checks widening before `UInt32` arithmetic.  `uint32ToUInt8Wrap` checks narrowing from `300` to `44`.  These conversions stay internal because exported `UInt8` and `UInt32` values remain outside the ABI.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 134 accepted, 15 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 134 accepted, 15 rejected, and 4 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Recursion Branch Orientation

The Nat-recursion extractor now accepts the conditional tail-call shape with the recursive call in either branch.  For `if cond then recursiveCall else exitValue`, the emitted loop continues while `cond` holds and fuel remains.  For the older `if cond then exitValue else recursiveCall` shape, the emitted loop continues while `cond` is false and fuel remains.

`LeanExe.Examples.Correctness.recThenBranchExitDemo` covers early exit from the new orientation.  `recThenBranchFuelDemo` covers fuel exhaustion in the same source shape.  Existing recursion examples still cover unconditional tail calls, let-bound recursive arguments, product-valued recursive arguments, and the original early-exit orientation.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 136 accepted, 15 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 136 accepted, 15 rejected, and 4 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: ByteArray FNV-1a Example

`LeanExe.Examples.ByteArrayPrograms.fnv1a32` computes the 32-bit FNV-1a checksum of a read-only `ByteArray` and returns it as `UInt64` at the public ABI boundary.  The program uses internal `UInt8` reads, `UInt8.toUInt32`, internal `UInt32` xor and multiplication, and the supported fuel-recursion shape over a byte buffer.  This gives the byte-array harness a small real byte-oriented program rather than only single-byte accessors.

The JavaScript harness computes expected values with `Math.imul` and unsigned 32-bit truncation.  The cases cover empty input, one byte, and a short multi-byte input.  The Lean program remains pure and does not add byte-array construction or mutation support.

Checks run:

- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 26 bytearray allocation cases`.
- [x] `node test/run_all.js` returned `checked 136 accepted, 15 rejected, and 4 trapped cases`, `checked 26 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Scalar Inequality

The extractor now lowers Lean’s `!=` notation, which elaborates to `bne`.  The lowering is the negation of the same scalar equality path used for `BEq.beq`.  It works both as a `Bool` expression and directly as a condition.

`LeanExe.Examples.Correctness.bneScalars` covers `UInt64` inequality in a branch.  `bneAsBool` covers a `Bool` entry result over bounded `Nat`.  `bneBool` covers inequality over `Bool` values.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 141 accepted, 15 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 141 accepted, 15 rejected, and 4 trapped cases`, `checked 26 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Bool.xor

The extractor now lowers `Bool.xor` through the condition extractor.  The lowering computes exclusive-or from existing condition forms: left and not right, or not left and right.  This keeps boolean normalization in the same path used by `&&`, `||`, and `!`.

`LeanExe.Examples.Correctness.boolXorValues` covers false/false, false/true, and true/true cases.  The entry returns `Bool`, so the harness checks the public boolean ABI as well as condition lowering.  No new IR operation was needed.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 144 accepted, 15 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 144 accepted, 15 rejected, and 4 trapped cases`, `checked 26 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Safe Indexing

The extractor now lowers `GetElem?.getElem?`, the elaborated form of `a[i]?`, for `Array UInt64` and `ByteArray`.  The lowering adds extractor-level structured lets so the array pointer, byte-array pointer and length, and index are bound once around the resulting `Option` tag and payload.  The `some` payload uses the existing bounds-checked load, but consumers only evaluate that payload when the tag is nonzero, so out-of-bounds safe indexing returns `none` without trapping.

This work also fixes generated `Option` matcher arm ordering.  Generated matcher declarations pass arms in source order, so a match written with the `some` arm first does not have the same argument order as a match written with the `none` arm first.  The extractor now classifies generated `Option` matcher arms by the lambda domain: `Unit` for `none`, and the payload type for `some`.

`LeanExe.Examples.Correctness.arrayGetQuestionRead` covers in-bounds and out-of-bounds `Array UInt64` safe indexing.  `arrayGetQuestionGetDSkipsDefaultTrap` checks default laziness after safe indexing.  `arrayGetQuestionNoneSkipsPayloadTrap` checks that the out-of-bounds path does not execute the payload load.  `optionSomeFirstMatch` directly covers generated `Option` matcher arm ordering.  `LeanExe.Examples.ByteArrayPrograms.byteAtQuestionOrZero` covers safe byte indexing through the byte-array ABI.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/core_correctness.js` returned `checked 149 accepted, 15 rejected, and 4 trapped cases`.
- [x] `node test/bytearray_alloc.js` returned `checked 29 bytearray allocation cases`.
- [x] `node test/run_all.js` returned `checked 149 accepted, 15 rejected, and 4 trapped cases`, `checked 29 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Bool Matcher Arm Order

Generated `Bool` matcher declarations pass arms in source order.  The extractor previously assumed the generated argument order was always false arm then true arm, which only holds when the source match lists `false` first.  The extractor now reads the generated matcher type and classifies each arm by whether its result type is indexed by `Bool.false` or `Bool.true`.

`LeanExe.Examples.Correctness.boolMatchTrueFirstScalar` covers a match written with the `true` arm first.  `boolMatchTrueFirstSkipsFalseTrap` checks branch laziness in the same source order, so a reversed lowering would execute the false arm and trap.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 152 accepted, 15 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 152 accepted, 15 rejected, and 4 trapped cases`, `checked 29 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Nonrecursive Nat Matches

The extractor now lowers nonrecursive zero/successor matches over bounded `Nat` values.  Generated `Nat` matchers have a `Unit` arm for zero and a `Nat` arm for successor, so the extractor classifies source-ordered arms by binder type.  The lowering binds the scrutinee once, returns the zero arm when it is zero, and passes `n - 1` to the successor arm when it is nonzero.

`LeanExe.Examples.Correctness.natMatchZero` covers the ordinary zero-first source order.  `natMatchSuccFirst` covers successor-first source order and checks that the predecessor value reaches the successor arm.  `natMatchZeroSkipsSuccTrap` and `natMatchSuccSkipsZeroTrap` check branch laziness.  `natMatchBoolCondition` covers a `Nat` match producing `Bool`, and `natMatchProduct` covers a structured product result.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 162 accepted, 15 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 162 accepted, 15 rejected, and 4 trapped cases`, `checked 29 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Report Classifier Alignment

The checked-environment report now uses the generic entry signature checker to render entry shapes instead of a small hard-coded set of shapes.  It also classifies implemented frontier primitives for internal products, internal `Option`, erased `Unit` values used by generated matchers, safe indexing, array append and extract, fixed-width conversions, and nonrecursive `Nat` matches.  This removes rejected frontier entries from reports for declarations that the compiler already accepts.

`test/report_classification.js` covers one `Nat` matcher entry, one byte-array safe-indexing entry, and one `Option`/product entry.  Each case checks that the report shows the expected entry shape, reports an implemented compile status, and contains no rejected frontier item.

Checks run:

- [x] `lake build`
- [x] `node test/report_classification.js` returned `checked 3 report classification cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 162 accepted, 15 rejected, and 4 trapped cases`, `checked 29 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Internal Unit Values

The generic compiler now admits `Unit` as an internal value type.  It represents `()` as scalar zero, accepts local `Unit` values, product fields containing `Unit`, and project-local helpers with `Unit` parameters or results.  The public ABI remains unchanged: entries with `Unit` parameters or `Unit` results are rejected.

`LeanExe.Examples.Correctness.unitProductSecond` covers `Unit` inside a product.  `unitHelperCall` covers an internal helper parameter of type `Unit`, and `unitResultIgnored` covers an internal helper result of type `Unit`.  `rejectUnitReturn` and `rejectUnitParam` keep the ABI boundary explicit.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 165 accepted, 17 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 165 accepted, 17 rejected, and 4 trapped cases`, `checked 29 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: UInt32 Division Coverage

The generic primitive path already lowered `UInt32` division and remainder through the same checked division and remainder operations used by `UInt64` and `UInt8`.  The specification did not state that support, and the correctness harness did not test it.  The tests now cover ordinary `UInt32` division and remainder and Lean’s zero-divisor behavior.

`LeanExe.Examples.Correctness.uint32DivMod` checks a nonzero divisor.  `uint32DivModZero` checks that `x / 0` returns `0` and `x % 0` returns `x`.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 167 accepted, 17 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 167 accepted, 17 rejected, and 4 trapped cases`, `checked 29 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Dependent If

The extractor now lowers `dite`, the elaborated form of `if h : p then ... else ...`.  The condition uses the existing proposition extractor, and both proof-lambda arms receive an erased scalar placeholder for the proof binder.  The emitted value uses the same branch-local behavior as ordinary `if`, so skipped dependent-if arms do not evaluate partial operations.

`LeanExe.Examples.Correctness.dependentIfNat` covers a bounded-`Nat` proposition.  `dependentIfSkipsElseTrap` and `dependentIfSkipsThenTrap` check branch laziness.  `dependentIfProduct` covers a structured product result.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 173 accepted, 17 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 173 accepted, 17 rejected, and 4 trapped cases`, `checked 29 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array Empty Constructors

The extractor now lowers `Array.empty`, `Array.mkEmpty`, `Array.emptyWithCapacity`, and `Array.singleton` for `Array UInt64`.  Empty constructors allocate an empty array.  The capacity argument is not extracted because the current array layout has no observable capacity, and Lean’s pure definitions of these constructors do not use that argument.  `Array.singleton` allocates one element through the existing replicate path.

`LeanExe.Examples.Correctness.arrayEmptyConstructors` covers the three empty constructors.  `arrayEmptyCapacitySkipsTrap` checks that an ignored capacity expression is not evaluated.  `arraySingletonRead` checks singleton size and element contents.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 176 accepted, 17 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 176 accepted, 17 rejected, and 4 trapped cases`, `checked 29 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: ByteArray Extract

The extractor now lowers `ByteArray.extract` as an internal read-only slice.  It binds the source pointer, source length, start, and stop once, clamps stop to the source length, returns an empty slice when start is outside the source or stop does not exceed start, and otherwise returns a pointer-length view into the original bytes.  Public `ByteArray` results remain outside the ABI.

`LeanExe.Examples.ByteArrayPrograms.sliceSecondPlusSize` checks reading through a nonempty slice and the empty result when start equals the source length.  `sliceClampSize` checks stop clamping, and `sliceStopBeforeStart` checks the empty case when stop precedes start.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 34 bytearray allocation cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 176 accepted, 17 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Nat Division Coverage

The extractor already lowered `Nat` division and remainder through the checked unsigned operation path.  The specification now states that bounded `Nat` division and remainder use Lean’s zero-divisor behavior: `x / 0` returns `0`, and `x % 0` returns `x`.

`LeanExe.Examples.Correctness.natDivModNormal` checks ordinary quotient and remainder results.  `natDivModZero` checks the zero-divisor case.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 179 accepted, 17 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 179 accepted, 17 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Product Pattern Matching

The extractor now lowers product pattern matching for ordinary generated matchers and direct `Prod.casesOn` applications, and it recognizes `Prod.rec` if a checked term contains it.  A product matcher arm receives the left and right fields as internal values, preserving the same field-level laziness used by product projection.  The demand summary path maps demanded arm binders back to the corresponding scrutinee fields, so a helper that destructures a pair and ignores one field does not force the ignored field.

`LeanExe.Examples.Correctness.productMatchDestructure` checks ordinary pair destructuring.  `productMatchUsesFirstOnly` checks that the ignored field does not trap.  `productMatchCondition` checks a product match used as a condition, and `productMatchNested` checks a product match returning a product.

An initial parallel `node test/core_correctness.js` run raced `lake build LeanExe.Examples.Correctness` and failed before compilation because the example module’s `.olean` file was not present.  The harness passed when rerun after the example build completed.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 183 accepted, 17 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 183 accepted, 17 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Option Fallback

The extractor now lowers `Option.orElse` and option `<|>` for internal `Option` values.  The fallback thunk receives an erased `Unit` value and is extracted only for the `none` arm.  The demand summary path treats the fallback as branch-local, so a helper that returns an existing `some` value does not force a trapping fallback.

`LeanExe.Examples.Correctness.optionOrElseNone` checks `<|>` on `none`.  `optionOrElseDirectSomeSkipsFallbackTrap` checks direct `Option.orElse` on `some` without evaluating the fallback, and `optionOrElseProduct` checks a structured payload.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 186 accepted, 17 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 186 accepted, 17 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Option Filter

The extractor now lowers `Option.filter` for internal `Option` values.  The predicate runs only for `some`, and it receives the payload as a lazy internal value.  Filtering a `some` value to `none` leaves the payload irrelevant, matching the existing tagged representation.

`LeanExe.Examples.Correctness.optionFilterSomeKeep` and `optionFilterSomeDrop` check the two predicate outcomes for `some`.  `optionFilterNoneSkipsPredicateTrap` checks that `none` skips a trapping predicate.  `optionFilterIgnoresPayloadTrap` checks that a predicate which ignores its argument does not force a trapping payload.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 190 accepted, 17 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 190 accepted, 17 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Structured Helper Inlining

Nonrecursive project-local helpers now inline directly from the checked environment when their source signature uses supported local types.  This separates helper inlining from the Wasm function list, whose emitted functions still use the scalar and array ABI.  The inline stack rejects recursive inline expansion, so recursive code continues through the existing recursion path rather than expanding without a bound.

`LeanExe.Examples.Correctness.productHelperResult` checks a helper returning a product, and `productHelperParamSkipsTrap` checks a product parameter with an ignored trapping field.  `optionHelperResult` and `optionHelperNone` check a helper returning `Option`, and `optionHelperParam` checks an `Option` parameter.

The first focused harness run failed on `productHelperResult` because the inline attempt still lived only in the scalar extraction path.  The value extractor now tries local helper inlining before falling back to scalar extraction, so structured helper results enter the extractor as structured values.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 195 accepted, 17 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 195 accepted, 17 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Internal Except Values

The extractor now lowers restricted internal `Except` values.  `Except.error` uses tag `0`, `Except.ok` uses tag `1`, and each value carries both an error payload and an ok payload so pattern matching can select the demanded arm.  `Except Unit α` remains rejected because the current internal type shape also represents `Option α` as `Unit ⊕ α`; the extractor needs source type identity before those two cases can share the same payload types without ambiguity.

`LeanExe.Examples.Correctness.exceptOkMatch`, `exceptOkFirstMatch`, and `exceptErrorMatch` check constructor ordering and generated matcher arm ordering.  `exceptErrorSkipsUnusedPayloadTrap` checks payload laziness, `exceptMatchCondition` checks a match used as a condition, and `exceptProductPayload` checks a structured ok payload.  `rejectExceptReturn` and `rejectExceptParam` keep the current ABI boundary explicit.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 201 accepted, 19 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 201 accepted, 19 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Except Map and Bind

The extractor now lowers `Except.map` and `Except.bind` for restricted internal `Except` values.  Both operations evaluate their function only for the `ok` case.  `Except.bind` preserves an existing error without evaluating the bind function, and it adopts the tag and payloads returned by the bind function for `ok`.

`LeanExe.Examples.Correctness.exceptMapOk`, `exceptMapErrorSkipsFunctionTrap`, and `exceptMapProduct` check mapping over `ok`, skipped mapping over `error`, and structured mapped payloads.  `exceptBindOk`, `exceptBindErrorSkipsFunctionTrap`, `exceptBindFunctionError`, and `exceptBindProduct` cover the corresponding bind cases.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 208 accepted, 19 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 208 accepted, 19 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Report Coverage for Structured Values

The report classification harness now includes entries that depend on structured helper inlining and restricted internal `Except` support.  `productHelperResult` checks an inline-only product helper signature, and `exceptBindProduct` checks the `Except` constructors, matcher, and bind classifier path.

Checks run:

- [x] `lake build`
- [x] `node test/report_classification.js` returned `checked 5 report classification cases`.
- [x] `node test/run_all.js` returned `checked 5 report classification cases`, `checked 208 accepted, 19 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Except Helper Coverage

The correctness suite now covers nonrecursive helpers with restricted `Except` parameters and results.  The specification also no longer describes structured outputs as waiting for `Except` to enter the core IR; `Except` is internal now, while public structured outputs still need a Wasm result ABI.

`LeanExe.Examples.Correctness.exceptHelperResult` and `exceptHelperError` check a helper returning restricted `Except`.  `exceptHelperParam` checks an `Except` parameter.

The first focused harness run failed on `exceptHelperResult` because the value-level `if` extractor still handled only ByteArray, product, and `Option`-shaped sum result types before falling back to scalar extraction.  The value-level `if` path now accepts every supported local result type.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 211 accepted, 19 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 5 report classification cases`, `checked 211 accepted, 19 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Except toOption

The extractor now lowers `Except.toOption` for restricted internal `Except` values.  The lowering reuses the `Except` tag as the `Option` tag and keeps only the ok payload, so an error payload is not needed when the resulting `Option` is inspected.

`LeanExe.Examples.Correctness.exceptToOptionOk` checks the ok path.  `exceptToOptionErrorSkipsPayloadTrap` checks that converting an error to `none` does not force an ignored trapping error payload.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 213 accepted, 19 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 5 report classification cases`, `checked 213 accepted, 19 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Except Fallback

The extractor now lowers `<|>` for restricted internal `Except` values through `HOrElse.hOrElse`.  The fallback thunk runs only for `error`; an existing `ok` value preserves its payload without evaluating the fallback.

`LeanExe.Examples.Correctness.exceptOrElseError` checks recovery from an error, `exceptOrElseOkSkipsFallbackTrap` checks fallback laziness for `ok`, and `exceptOrElseFallbackError` checks a fallback that also returns an error.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 216 accepted, 19 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 5 report classification cases`, `checked 216 accepted, 19 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Except Unit Rejection

The correctness suite now checks the documented rejection of `Except Unit α`.  The current internal type representation uses `Unit ⊕ α` for `Option α`, so accepting `Except Unit α` would require the extractor to preserve source type identity rather than relying on the current structural sum type alone.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 216 accepted, 20 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 5 report classification cases`, `checked 216 accepted, 20 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Except Specification Alignment

Several summary rows in `spec.md` still described only product and `Option` support after restricted `Except` entered the internal value fragment.  The summary rows now mention restricted `Except` for local lets, constructors, pattern matching, and report classification.

Checks run:

- [x] Documentation-only change; no build required.

## 2026-05-07: Proof-Indexed GetElem

The extractor now lowers `GetElem.getElem`, the checked term behind proof-indexed `a[i]` and `input[i]`.  The proof argument is erased, and the runtime load uses the same checked array or byte-array load path as partial indexing.  This lets source code use ordinary proof-indexed indexing when Lean can supply or carry the bounds proof.

`LeanExe.Examples.Correctness.arrayGetProof` checks `Array UInt64` proof-indexed reads.  `LeanExe.Examples.ByteArrayPrograms.byteAtProofOrZero` checks proof-indexed `ByteArray` reads under a dependent-if bounds proof.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/core_correctness.js` returned `checked 217 accepted, 20 rejected, and 4 trapped cases`.
- [x] `node test/bytearray_alloc.js` returned `checked 36 bytearray allocation cases`.
- [x] `node test/run_all.js` returned `checked 5 report classification cases`, `checked 217 accepted, 20 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Pure Id Run

The extractor now erases `Id.run` and `Pure.pure` when the monad argument is `Id`.  This supports simple pure `do` blocks that elaborate to `Id.run do ... return value`.  General monadic bind, loops, and effectful `do` blocks remain outside this step.

`LeanExe.Examples.Correctness.idRunLet` checks a simple pure return.  `idRunSkipsUnusedLetTrap` checks that the existing lazy-let behavior still skips an unused trapping binding inside the `Id` block.  `idRunCondition` checks a pure `Id` block used as a condition.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 220 accepted, 20 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 5 report classification cases`, `checked 220 accepted, 20 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Pure Id Bind

The extractor now erases `Bind.bind` when the monad argument is `Id`.  The bound value enters the continuation as a lazy internal value, matching the extractor’s existing lazy-let behavior for ignored bindings.  This supports simple pure `do` blocks with `let x ← pure value`.

`LeanExe.Examples.Correctness.idRunBind` checks a pure bind in an `Id.run` block.  `idRunBindSkipsUnusedTrap` checks that an ignored bound value does not force a trapping expression.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 222 accepted, 20 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 5 report classification cases`, `checked 222 accepted, 20 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Report Coverage for Pure Id

The report classification harness now includes `LeanExe.Examples.Correctness.idRunBind`, so the classifier checks the `Id.run`/`Pure.pure`/`Bind.bind` frontier used by simple pure `do` notation.

Checks run:

- [x] `lake build`
- [x] `node test/report_classification.js` returned `checked 6 report classification cases`.
- [x] `node test/run_all.js` returned `checked 6 report classification cases`, `checked 222 accepted, 20 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Simple let mut Coverage

Lean elaborates simple `let mut` assignment inside `Id.run` to ordinary shadowing lets, which the extractor already supports.  The correctness suite now covers that source style so it does not regress while pure `Id` support grows.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 223 accepted, 20 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 6 report classification cases`, `checked 223 accepted, 20 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Pure Id Loop Rejection

The correctness suite now checks that a pure `for` loop inside `Id.run` remains rejected.  Lean elaborates the loop body to a function that returns `ForInStep`, which the current extractor does not lower.  This keeps the pure `do` support limited to `Id.run`, `Pure.pure`, `Bind.bind`, and let-style code.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 223 accepted, 21 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 6 report classification cases`, `checked 223 accepted, 21 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Structured Pure Id Bind Coverage

The correctness suite now covers `Id.run do let x ← pure ...` when the bound value is a product, an `Option`, or a restricted `Except`.  The extractor already routes `Id` binds through the general value extractor, so these tests confirm that pure `do` notation preserves the existing structured-value behavior instead of only scalar bindings.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 226 accepted, 21 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 6 report classification cases`, `checked 226 accepted, 21 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Except isOk

Lean 4.29 exposes `Except.isOk : Except ε α -> Bool`.  The extractor now lowers it for restricted internal `Except` values by reading the existing tag, so the payload of `Except.ok bad` is not extracted when the program only asks whether the value is ok.

An initial parallel `node test/report_classification.js` run raced `lake build LeanExe.Examples.Correctness` and failed because the example module’s `.olean` file was not present yet.  The report harness passed when rerun after the example build completed.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 7 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 229 accepted, 21 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 7 report classification cases`, `checked 229 accepted, 21 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Except mapError

Lean 4.29 exposes `Except.mapError : (ε -> ε') -> Except ε α -> Except ε' α`.  The extractor now lowers it for restricted internal `Except` values.  The mapping function runs only for `error`, and `ok` preserves its payload without evaluating the mapping function.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 8 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 232 accepted, 21 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 8 report classification cases`, `checked 232 accepted, 21 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: UInt64 toNat Coverage

The correctness suite now covers `UInt64.toNat` directly and through method notation.  The method-notation case uses `UInt64` maximum to check that the bounded `Nat` representation preserves the full 64-bit value at the ABI boundary.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 234 accepted, 21 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 8 report classification cases`, `checked 234 accepted, 21 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Option get!

Lean 4.29 defines `Option.get!` as a panic on `none`, not as an `Inhabited` default.  The IR now has an explicit trap expression, and the extractor lowers `Option.get!` by selecting the payload for `some` and the trap expression for `none`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 9 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 237 accepted, 21 rejected, and 5 trapped cases`.
- [x] `node test/run_all.js` returned `checked 9 report classification cases`, `checked 237 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Option any and all

The extractor now lowers `Option.any` and `Option.all` for internal `Option` values.  Both operations evaluate their predicate only for `some`; `any` returns false for `none`, and `all` returns true for `none`, matching Lean’s definitions.  The report classifier also recognizes `UInt64.decLt`, which appears as the decidable instance for a supported `UInt64` comparison inside an `Option.any` predicate.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 10 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 241 accepted, 21 rejected, and 5 trapped cases`.
- [x] `node test/run_all.js` returned `checked 10 report classification cases`, `checked 241 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Bool toNat

The extractor now lowers `Bool.toNat`.  The current scalar representation already stores false as `0` and true as `1`, so the lowering preserves the existing expression.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 11 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 243 accepted, 21 rejected, and 5 trapped cases`.
- [x] `node test/run_all.js` returned `checked 11 report classification cases`, `checked 243 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Nat Boolean Comparisons

The extractor now lowers `Nat.blt` and `Nat.ble` as Boolean comparisons over the bounded `Nat` representation.  This covers code that calls the named Boolean comparison functions instead of using proposition comparisons in an `if`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 12 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 248 accepted, 21 rejected, and 5 trapped cases`.
- [x] `node test/run_all.js` returned `checked 12 report classification cases`, `checked 248 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Nat Boolean Equality

The extractor now lowers `Nat.beq` as Boolean equality over the bounded `Nat` representation.  The correctness suite covers both direct Bool results and conditions that branch on the named equality function.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 13 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 252 accepted, 21 rejected, and 5 trapped cases`.
- [x] `node test/run_all.js` returned `checked 13 report classification cases`, `checked 252 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array Append Notation

The extractor now lowers `HAppend.hAppend` for `Array UInt64`, so source code can use `left ++ right` instead of calling `Array.append` directly.  The lowering reuses the existing copy-on-write array append IR operation.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 14 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 253 accepted, 21 rejected, and 5 trapped cases`.
- [x] `node test/run_all.js` returned `checked 14 report classification cases`, `checked 253 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array back?

The extractor now lowers `Array.back?` for `Array UInt64`.  The emitted value is an internal `Option`: empty arrays produce `none`, and nonempty arrays produce `some` with the last element.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 15 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 255 accepted, 21 rejected, and 5 trapped cases`.
- [x] `node test/run_all.js` returned `checked 15 report classification cases`, `checked 255 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array modify

The extractor now lowers `Array.modify` for `Array UInt64`.  In-bounds modification reads the old element, applies the source lambda, and emits the existing copy-on-write array update.  Out-of-bounds modification returns the original array and does not evaluate the lambda.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 16 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 257 accepted, 21 rejected, and 5 trapped cases`.
- [x] `node test/run_all.js` returned `checked 16 report classification cases`, `checked 257 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array insertIdxIfInBounds

The extractor now lowers `Array.insertIdxIfInBounds` for `Array UInt64`.  The IR has a dedicated insertion expression so the emitter can evaluate the array and index first, then evaluate the inserted value only when `index <= size`.  In-bounds insertion allocates a fresh array, copies the prefix, writes the inserted value, and copies the suffix one slot to the right.  Out-of-bounds insertion returns the original array.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 17 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 260 accepted, 21 rejected, and 5 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayInsertIdxIfInBoundsSkipsValueTrap --out .lake/build/core-correctness/arrayInsertIdxIfInBoundsSkipsValueTrap.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayInsertIdxIfInBoundsSkipsValueTrap .lake/build/core-correctness/arrayInsertIdxIfInBoundsSkipsValueTrap.wat` returned `7`.
- [x] `node test/run_all.js` returned `checked 17 report classification cases`, `checked 260 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array eraseIdxIfInBounds

The extractor now lowers `Array.eraseIdxIfInBounds` for `Array UInt64`.  In-bounds erasure allocates a fresh array with one fewer element, copies the prefix, and copies the suffix one slot to the left.  Out-of-bounds erasure returns the original array.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 18 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 263 accepted, 21 rejected, and 5 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayEraseIdxIfInBoundsMiddle --out .lake/build/core-correctness/arrayEraseIdxIfInBoundsMiddle.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayEraseIdxIfInBoundsMiddle .lake/build/core-correctness/arrayEraseIdxIfInBoundsMiddle.wat` returned `132`.
- [x] `node test/run_all.js` returned `checked 18 report classification cases`, `checked 263 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array swapIfInBounds

The extractor now lowers `Array.swapIfInBounds` for `Array UInt64`.  It evaluates the array and both indices once, returns the original array when either index is out of bounds, and otherwise allocates a fresh array, copies the cells, and writes both swapped elements from the original array.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 19 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 266 accepted, 21 rejected, and 5 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arraySwapIfInBoundsEnds --out .lake/build/core-correctness/arraySwapIfInBoundsEnds.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arraySwapIfInBoundsEnds .lake/build/core-correctness/arraySwapIfInBoundsEnds.wat` returned `4231`.
- [x] `node test/run_all.js` returned `checked 19 report classification cases`, `checked 266 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array reverse

The extractor now lowers `Array.reverse` for `Array UInt64`.  Arrays with length zero or one return the original pointer, matching the exposed Lean definition.  Longer arrays allocate a fresh array and copy source cells in reverse order.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 20 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 268 accepted, 21 rejected, and 5 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayReverseRead --out .lake/build/core-correctness/arrayReverseRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayReverseRead .lake/build/core-correctness/arrayReverseRead.wat` returned `321`.
- [x] `node test/run_all.js` returned `checked 20 report classification cases`, `checked 268 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Proof-indexed Array updates

The extractor now lowers proof-indexed `Array.insertIdx`, `Array.eraseIdx`, and `Array.swap` for `Array UInt64`.  It erases proof arguments and reuses the existing in-bounds insert, erase, and swap operations.  The report now omits dependencies of expanded theorem declarations from the runtime frontier, so generated proof declarations do not introduce rejected external dependencies.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 21 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 271 accepted, 21 rejected, and 5 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayProofInsertIdxRead --out .lake/build/core-correctness/arrayProofInsertIdxRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayProofInsertIdxRead .lake/build/core-correctness/arrayProofInsertIdxRead.wat` returned `123`.
- [x] `node test/run_all.js` returned `checked 21 report classification cases`, `checked 271 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Identity function

The extractor now erases `id` for supported first-fragment values.  The scalar path covers ordinary identity applications, and the structured-value path preserves product laziness, so projecting one field of `id (bad, value)` does not force the unused field.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 22 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 273 accepted, 21 rejected, and 5 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.idFunctionUInt64 --out .lake/build/core-correctness/idFunctionUInt64.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke idFunctionUInt64 .lake/build/core-correctness/idFunctionUInt64.wat 4` returned `5`.
- [x] `node test/run_all.js` returned `checked 22 report classification cases`, `checked 273 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Proof-indexed Array back

The extractor now lowers proof-indexed `Array.back` for `Array UInt64`.  It erases the nonempty proof and emits the same last-element read used by `Array.back!`; unlike `back!`, the demand analysis treats the proof-indexed form as nontrapping because Lean has checked the nonempty proof.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 23 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 274 accepted, 21 rejected, and 5 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayProofBackRead --out .lake/build/core-correctness/arrayProofBackRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayProofBackRead .lake/build/core-correctness/arrayProofBackRead.wat` returned `9`.
- [x] `node test/run_all.js` returned `checked 23 report classification cases`, `checked 274 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array insertIdx! and eraseIdx!

The extractor now lowers `Array.insertIdx!` and `Array.eraseIdx!` for `Array UInt64`.  Both operations bind the array and index once, branch on the bounds check, and use `trap` for the panic branch.  `Array.insertIdx!` keeps the inserted value inside the in-bounds branch, matching the exposed Lean definition.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 24 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 276 accepted, 21 rejected, and 7 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayInsertIdxBangRead --out .lake/build/core-correctness/arrayInsertIdxBangRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayInsertIdxBangRead .lake/build/core-correctness/arrayInsertIdxBangRead.wat` returned `123`.
- [x] `node test/run_all.js` returned `checked 24 report classification cases`, `checked 276 accepted, 21 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array set variants

The extractor now lowers proof-indexed `Array.set` and total `Array.setIfInBounds` for `Array UInt64`.  `Array.set` erases the proof and uses the existing copy-on-write replacement path.  `Array.setIfInBounds` binds the array and index once, returns the original array when the index is out of bounds, and evaluates the replacement value only when the index is in bounds.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 25 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 279 accepted, 21 rejected, and 7 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arraySetIfInBoundsSkipsValueTrap --out .lake/build/core-correctness/arraySetIfInBoundsSkipsValueTrap.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arraySetIfInBoundsSkipsValueTrap .lake/build/core-correctness/arraySetIfInBoundsSkipsValueTrap.wat` returned `7`.
- [x] `node test/run_all.js` returned `checked 25 report classification cases`, `checked 279 accepted, 21 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-08: Array swapAt

The extractor now lowers proof-indexed `Array.swapAt` for `Array UInt64`.  The operation erases its proof argument and returns an internal product whose first field reads the old element and whose second field is the copy-on-write updated array.  Lean 4.29 evaluates both the inline and let-bound `.1` projections without evaluating a replacement value that would panic, so the extractor preserves that product projection behavior.

Checks run:

- [x] `lake env lean /tmp/leanexe_swapAt_inline_check.lean` returned `2`.
- [x] `lake env lean /tmp/leanexe_swapAt_let_check.lean` returned `2`.
- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 26 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 282 accepted, 21 rejected, and 7 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arraySwapAtLetFirstSkipsValueTrap --out .lake/build/core-correctness/arraySwapAtLetFirstSkipsValueTrap.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arraySwapAtLetFirstSkipsValueTrap .lake/build/core-correctness/arraySwapAtLetFirstSkipsValueTrap.wat` returned `2`.
- [x] `node test/run_all.js` returned `checked 26 report classification cases`, `checked 282 accepted, 21 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-08: Array map

The extractor now lowers `Array.map` for `Array UInt64` when the mapping function is a one-argument lambda returning `UInt64`.  The IR keeps a dedicated array-map expression with an explicit item slot for the mapped element.  CoreWasm evaluates the source array once, allocates a fresh result array with the same length, loads each source cell in index order, evaluates the mapper body with that cell bound to the item slot, and stores the mapped value into the result.  Empty arrays return an empty result without evaluating the mapper body.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 285 accepted, 21 rejected, and 7 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 27 report classification cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayMapEmptySkipsFunctionTrap --out .lake/build/core-correctness/arrayMapEmptySkipsFunctionTrap.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayMapEmptySkipsFunctionTrap .lake/build/core-correctness/arrayMapEmptySkipsFunctionTrap.wat` returned `0`.
- [x] `node test/run_all.js` returned `checked 27 report classification cases`, `checked 285 accepted, 21 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-08: Structure result ABI design

The next implementation area is user-defined structures and returned structure values.  Lean 4.29 exposes the structure metadata needed for this through `Lean/Structure.lean`: `StructureInfo`, `getStructureInfo?`, `getStructureFieldsFlattened`, projection-function metadata, and `isStructureLike`.  The design in `spec.md` now fixes the direction before implementation: preserve source structure identity in the extractor, use Lean's flattened field order for layout, and flatten supported public fields to Wasm multi-value results at the ABI boundary.

Planned implementation sequence:

- [x] Add a structure-aware type form that records the source structure name and ordered runtime fields.
- [x] Extract constructor applications, projections, and structure update elaborations through that field representation.
- [x] Replace the single-result function ABI with a shared flattening path for public returns.
- [x] Emit Wasm function result vectors for flattened structure returns.
- [x] Add correctness cases for a returned scalar structure, nested structure fields, field projection laziness, and array fields in returned structures.
- [x] Add proof-field erasure and single-constructor structure matcher extraction after the extractor has explicit rules for proposition fields and recursor argument layout.

## 2026-05-08: User structures and multi-result returns

The extractor now has source-identified structure values through `Ty.struct` and an extractor-level structure value that records the Lean structure name and ordered fields.  The implemented slice accepts monomorphic, nonrecursive structures with supported runtime fields, lowers constructor applications and projection functions through Lean metadata, preserves lazy projection behavior for unused fields, and flattens exported structure results to Wasm multi-value result vectors.  The implementation deliberately leaves proof-field erasure, polymorphic structures, recursive structures, inherited-field flattening, structure entry parameters, and structure recursor matching unsupported until those cases have explicit rules.

The correctness examples now cover field projection laziness, structure update syntax, a nonrecursive helper returning a structure, direct structure returns, branch-selected structure returns, nested structure returns, and a returned structure that contains an `Array UInt64` field.  The JavaScript harness compares multi-value Wasm returns and validates array-field results by reading the returned array pointer in exported memory rather than asserting a specific allocation address.  A direct WAT check for `structureReturn` shows `(result i64 i64)`, and Wasmtime returns `5` and `6` for input `4`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 28 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 293 accepted, 22 rejected, and 7 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.structureReturn --out .lake/build/core-correctness/structureReturn.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke structureReturn .lake/build/core-correctness/structureReturn.wat 4` returned `5` and `6`.
- [x] `node test/run_all.js` returned `checked 28 report classification cases`, `checked 293 accepted, 22 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-08: Structure matchers and proof fields

The structure extractor now classifies each constructor field as either a runtime field or an erased proof field.  The proof test handles direct `Prop` fields and fully applied constants whose declared result is `Prop`, which covers ordinary equality proofs such as `ok : value = value` without requiring runtime representation.  Runtime field indices now map from Lean source field indices to compact runtime indices, so projections and matcher binders skip erased fields while preserving source field order for the fields that remain.

Single-constructor structure matching now lowers through the same field representation as projections.  Direct structure recursors and generated matchers bind every source field in the arm; proof binders receive an erased placeholder, while runtime binders receive lazy field values.  This keeps `match ({ x := good, y := bad } : Point) with | { x, y := _ } => x` from emitting the unused `y` expression.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 29 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 299 accepted, 22 rejected, and 7 trapped cases`.
- [x] `node test/run_all.js` returned `checked 29 report classification cases`, `checked 299 accepted, 22 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: User inductive values

The extractor now accepts monomorphic, nonrecursive user-defined inductives that are not structures and have no indices or type parameters.  `Ty.variant` records the source inductive name and constructor payload types, and the extracted value records the source name, tag expression, and payload values for every constructor.  Constructor applications erase proof fields and fill inactive constructor payloads with default values.  Generated matchers and direct recursors bind source fields in constructor order; erased proof fields receive the existing zero placeholder, while runtime fields remain lazy payload values.

Exported user-inductive results now use a fixed tagged ABI: tag first, followed by flattened payload slots for each constructor in declaration order.  A nullary enum returns one `i64` tag.  A two-constructor status type with one `UInt64` payload in each constructor returns three `i64` values: tag, first-constructor payload, and second-constructor payload.  Entry parameters for user inductives remain rejected until the public input ABI has structured tagged input rules.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.statusBranchReturn --out .lake/build/core-correctness/statusBranchReturn.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke statusBranchReturn .lake/build/core-correctness/statusBranchReturn.wat 0` returned `0`, `5`, and `0`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke statusBranchReturn .lake/build/core-correctness/statusBranchReturn.wat 1` returned `1`, `0`, and `9`.
- [x] `node test/report_classification.js` returned `checked 31 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 312 accepted, 23 rejected, and 7 trapped cases`.
- [x] `node test/run_all.js` returned `checked 31 report classification cases`, `checked 312 accepted, 23 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Source-identified Except

`Except` now uses the `Ty.variant` path internally instead of the previous anonymous `sum` shape.  This separates `Except Unit α` from `Option α`, removing the old ambiguity where both types looked like `Unit ⊕ α` inside the extractor.  The public ABI still rejects `Except` parameters and results; this change only affects internal values, helper parameters, helper results, pattern matching, mapping, binding, conversion to `Option`, tag tests, and fallback.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 31 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 315 accepted, 22 rejected, and 7 trapped cases`.
- [x] `node test/run_all.js` returned `checked 31 report classification cases`, `checked 315 accepted, 22 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Source-identified Option

`Option` now uses the same `Ty.variant` and `ExtractedValue.variant` path as user-defined inductives and `Except`.  The extractor removed the dedicated `ExtractedValue.option` case.  `none` is represented by tag `0` with no constructor fields, and `some` is represented by tag `1` with one payload field.  Public `Option` parameters and results remain rejected until the public tagged ABI admits them.

This completes the internal representation part of the unified sum work for built-in `Option` and `Except`.  Remaining ABI work must decide how hosts pass and receive tagged values, including inactive payload slots and flattening order, before those values can cross exported function boundaries.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 31 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 315 accepted, 22 rejected, and 7 trapped cases`.
- [x] `node test/run_all.js` returned `checked 31 report classification cases`, `checked 315 accepted, 22 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Option and Except result ABI

Exported `Option` and `Except` results now use the same tagged multi-value ABI as source-defined inductive results.  `Option α` returns the tag followed by flattened payload slots for the `some` constructor.  `Except ε α` returns the tag, flattened error payload slots, and flattened success payload slots.  Inactive payload slots use the default values already used by source-defined inductive results.

The implementation keeps `Option` and `Except` entry parameters rejected.  Result support only relies on the existing output flattener; input support still needs source-order decoding rules for tagged parameter slots.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.optionReturn --out .lake/build/core-correctness/optionReturn.wat`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.exceptPointReturn --out .lake/build/core-correctness/exceptPointReturn.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke optionReturn .lake/build/core-correctness/optionReturn.wat 0` returned `0` and `0`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke optionReturn .lake/build/core-correctness/optionReturn.wat 3` returned `1` and `7`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke exceptPointReturn .lake/build/core-correctness/exceptPointReturn.wat 0` returned `0`, `7`, `0`, and `0`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke exceptPointReturn .lake/build/core-correctness/exceptPointReturn.wat 5` returned `1`, `0`, `5`, and `6`.
- [x] `node test/report_classification.js` returned `checked 33 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 323 accepted, 20 rejected, and 7 trapped cases`.
- [x] `node test/run_all.js` returned `checked 33 report classification cases`, `checked 323 accepted, 20 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Structured entry parameters

Entry parameter support now recurses through supported structures and tagged values.  Structure parameters flatten runtime fields in Lean field order after proof-field erasure.  Tagged parameters use the same slot order as tagged results: tag first, followed by each constructor's flattened payload slots in declaration order.  This admits monomorphic nonrecursive structure parameters, user-inductive parameters, `Option` parameters, and `Except` parameters when their runtime fields fit the current ABI.

The implementation reuses the existing `sourceParamBindings` path, which already reconstructed structured extractor values from flattened parameter slots.  The code change is therefore the signature gate, plus report classification for local user-inductive `casesOn` helpers generated by pattern matching on public tagged parameters.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.structureParam --out .lake/build/core-correctness/structureParam.wat`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.statusParam --out .lake/build/core-correctness/statusParam.wat`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.optionPointParam --out .lake/build/core-correctness/optionPointParam.wat`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.exceptParam --out .lake/build/core-correctness/exceptParam.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke structureParam .lake/build/core-correctness/structureParam.wat 2 3` returned `23`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke statusParam .lake/build/core-correctness/statusParam.wat 0 5 0` returned `15`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke optionPointParam .lake/build/core-correctness/optionPointParam.wat 1 3 4` returned `7`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke exceptParam .lake/build/core-correctness/exceptParam.wat 1 0 5` returned `5`.
- [x] `node test/report_classification.js` returned `checked 38 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 333 accepted, 16 rejected, and 7 trapped cases`.
- [x] `node test/run_all.js` returned `checked 38 report classification cases`, `checked 333 accepted, 16 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Scalar array element types

The array representation now admits every element type that fits the existing one-cell array layout: `Bool`, `UInt8`, `UInt32`, `UInt64`, and bounded `Nat`.  Each element still occupies one eight-byte cell in linear memory.  `UInt8` and `UInt32` keep their constrained scalar representations inside that cell, `Bool` uses `0` or `1`, and `Nat` uses the bounded runtime representation.  This preserves the existing copy-on-write array operations without changing indexing, copying, or returned-pointer behavior.

Arrays of structures and tagged values remain planned.  They need a multi-slot element layout before implementation: element width, copy loops, field access, inactive payload slots, and host decoding must be specified together.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build`
- [x] `node test/report_classification.js` returned `checked 42 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 339 accepted, 17 rejected, and 7 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayUInt8Read --out .lake/build/core-correctness/arrayUInt8Read.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayUInt8Read .lake/build/core-correctness/arrayUInt8Read.wat` returned `1044`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayUInt32MapRead --out .lake/build/core-correctness/arrayUInt32MapRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayUInt32MapRead .lake/build/core-correctness/arrayUInt32MapRead.wat` returned `3`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayBoolRead --out .lake/build/core-correctness/arrayBoolRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayBoolRead .lake/build/core-correctness/arrayBoolRead.wat` returned `1`.
- [x] `node test/run_all.js` returned `checked 42 report classification cases`, `checked 339 accepted, 17 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Fixed-width structure and tagged arrays

The IR and Wasm emitters now have explicit fixed-width array operations: allocation with an element width, slot-addressed reads, and slot-wise copy-on-write replacement.  The linear-memory layout keeps the length header at offset `0`.  Slot `s` of element `i` lives at cell index `1 + i * width + s`.  Scalar arrays are the width-one case.  Structure arrays flatten runtime fields in Lean field order after proof erasure.  Tagged arrays store the tag first, followed by every constructor payload slot in declaration order, matching the public tagged ABI.

The extractor now accepts fixed-width structure and tagged array literals, empty constructors, singleton construction, indexed reads, safe indexed reads, `back`, `back!`, `back?`, `set`, `set!`, `setIfInBounds`, `swapAt`, and returned pointers.  The older scalar-only copy operations now reject multi-slot arrays instead of compiling through one-cell loops.  Multi-slot `replicate`, `push`, `pop`, `append`, `extract`, insertion, erasure, swapping, reversal, modification, and mapping remain planned.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build`
- [x] `node test/report_classification.js` returned `checked 46 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 345 accepted, 18 rejected, and 7 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayStructureLiteralRead --out .lake/build/core-correctness/arrayStructureLiteralRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayStructureLiteralRead .lake/build/core-correctness/arrayStructureLiteralRead.wat` returned `1234`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayStatusLiteralMatch --out .lake/build/core-correctness/arrayStatusLiteralMatch.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayStatusLiteralMatch .lake/build/core-correctness/arrayStatusLiteralMatch.wat` returned `57`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.structurePointArrayReturn --out .lake/build/core-correctness/structurePointArrayReturn.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke structurePointArrayReturn .lake/build/core-correctness/structurePointArrayReturn.wat` returned `4176` and `2`.
- [x] `node test/run_all.js` returned `checked 46 report classification cases`, `checked 345 accepted, 18 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Multi-slot array push, pop, append, and extract

Fixed-width arrays now lower `push`, `pop`, `append`, and `extract` for structure and tagged elements.  The IR records the element width for each operation.  The emitters allocate by payload-cell count rather than element count: `push` copies the original payload cells and writes the new element slots, `pop` copies all but the final element, `append` copies the left cells followed by the right cells, and `extract` converts the requested element range into source and destination cell offsets.

The extractor routes these operations through the multi-slot path whenever the element type has a fixed width.  Scalar arrays still use the existing one-cell operations.  Multi-slot `replicate`, `getD`, insertion, erasure, swapping, reversal, modification, and mapping remain planned.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build`
- [x] `node test/report_classification.js` returned `checked 48 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 349 accepted, 17 rejected, and 7 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayStructureAppendRead --out .lake/build/core-correctness/arrayStructureAppendRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayStructureAppendRead .lake/build/core-correctness/arrayStructureAppendRead.wat` returned `1234`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayStructureExtractRead --out .lake/build/core-correctness/arrayStructureExtractRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayStructureExtractRead .lake/build/core-correctness/arrayStructureExtractRead.wat` returned `3456`.
- [x] `node test/run_all.js` returned `checked 48 report classification cases`, `checked 349 accepted, 17 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Multi-slot array insertion, erasure, swap, and reverse

Fixed-width arrays now lower bounded insertion, bounded erasure, bounded swaps, and reversal for structure and tagged elements.  The new IR nodes record element width, and the emitters copy by payload-cell offset.  Insertion copies the prefix, writes the flattened inserted value, and copies the suffix after the inserted element.  Erasure copies the prefix and shifts the suffix left by one element.  Swap copies the full payload and rewrites each selected element slot from the original array.  Reverse iterates by element index so slot order inside each element stays unchanged.

This completes the straightforward fixed-width copy operations for structure and tagged arrays.  Multi-slot `replicate`, `getD`, `modify`, and `map` remain planned because each needs an additional value-evaluation rule rather than only a copy-loop generalization.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build`
- [x] `node test/report_classification.js` returned `checked 51 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 356 accepted, 17 rejected, and 7 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayStructureReverseRead --out .lake/build/core-correctness/arrayStructureReverseRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayStructureReverseRead .lake/build/core-correctness/arrayStructureReverseRead.wat` returned `563412`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayStatusReverseMatch --out .lake/build/core-correctness/arrayStatusReverseMatch.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayStatusReverseMatch .lake/build/core-correctness/arrayStatusReverseMatch.wat` returned `1175`.
- [x] `node test/run_all.js` returned `checked 51 report classification cases`, `checked 356 accepted, 17 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Multi-slot array getD and modify

Fixed-width arrays now lower `Array.getD` and `Array.modify` for structure and tagged elements.  `Array.getD` is handled in the structured-value extractor, so the default value is selected field-by-field only when the index is out of bounds.  `Array.modify` loads the old element as a structured value, passes it to the source lambda, flattens the returned value, and lowers the update through the fixed-width copy-on-write replacement operation.

The remaining fixed-width array gaps are `Array.replicate` and `Array.map`.  Both need explicit value-evaluation rules in addition to slot copying: replication should evaluate the source value once and copy its flattened slots into each element, while mapping must define the result element layout and bind a structured source element in each loop iteration.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build`
- [x] `node test/report_classification.js` returned `checked 54 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 361 accepted, 17 rejected, and 7 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayStructureGetDSkipsDefaultTrap --out .lake/build/core-correctness/arrayStructureGetDSkipsDefaultTrap.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayStructureGetDSkipsDefaultTrap .lake/build/core-correctness/arrayStructureGetDSkipsDefaultTrap.wat` returned `12`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayStatusModifyMatch --out .lake/build/core-correctness/arrayStatusModifyMatch.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayStatusModifyMatch .lake/build/core-correctness/arrayStatusModifyMatch.wat` returned `107`.
- [x] `node test/run_all.js` returned `checked 54 report classification cases`, `checked 361 accepted, 17 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Multi-slot array replicate

Fixed-width arrays now lower `Array.replicate` for structure and tagged elements.  The lowering evaluates the length and element value once, stores the flattened element slots in locals, allocates `length * width` payload cells, and writes the stored slots into each element position.  This keeps replication aligned with the fixed-width memory layout used by literals and copy-on-write updates.

The remaining fixed-width array gap is `Array.map`.  It needs the mapper body to receive a structured source element inside the loop and the result array to use the mapped element type's width, which is a distinct lowering from scalar `Array.map`.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build`
- [x] `node test/report_classification.js` returned `checked 56 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 363 accepted, 17 rejected, and 7 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayStructureReplicateRead --out .lake/build/core-correctness/arrayStructureReplicateRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayStructureReplicateRead .lake/build/core-correctness/arrayStructureReplicateRead.wat` returned `1212`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayStatusReplicateMatch --out .lake/build/core-correctness/arrayStatusReplicateMatch.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayStatusReplicateMatch .lake/build/core-correctness/arrayStatusReplicateMatch.wat` returned `1077`.
- [x] `node test/run_all.js` returned `checked 56 report classification cases`, `checked 363 accepted, 17 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Multi-slot array map

Fixed-width arrays now lower `Array.map` for structure and tagged elements.  The IR records the source element width, result element width, source slot-local start, and flattened result expressions.  The emitters load each source element into local slots, evaluate the mapper body against that structured value, and store the flattened result slots into a freshly allocated result array.

This completes the planned fixed-width array operation set for monomorphic nonrecursive structures and small tagged values.  Nested arrays, polymorphic arrays, recursive element types, and owned byte-array results remain outside this slice.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build`
- [x] `node test/report_classification.js` returned `checked 58 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 366 accepted, 17 rejected, and 7 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayStructureMapRead --out .lake/build/core-correctness/arrayStructureMapRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayStructureMapRead .lake/build/core-correctness/arrayStructureMapRead.wat` returned `3375`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayStatusMapMatch --out .lake/build/core-correctness/arrayStatusMapMatch.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke arrayStatusMapMatch .lake/build/core-correctness/arrayStatusMapMatch.wat` returned `1168`.
- [x] `node test/run_all.js` returned `checked 58 report classification cases`, `checked 366 accepted, 17 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Structured Nat-fuel recursion results

The Nat-fuel recursion extractor now handles supported structured result values.  Base and early-exit arms lower through `extractValueFrom`, the final loop result uses structured `valueIte` when the recursion has an early-exit arm, and the exported function result flattens through the normal ABI path.  This admits recursive functions returning structures, user-defined tagged values, `Option`, or `Except` when the result fields fit the current ABI.

This does not broaden the accepted recursive call shape.  The successor arm still must tail-call the same recursive handle directly or place that tail call in one branch of the immediate `if`.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build`
- [x] `node test/report_classification.js` returned `checked 60 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 369 accepted, 17 rejected, and 7 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.recPointFuel --out .lake/build/core-correctness/recPointFuel.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke recPointFuel .lake/build/core-correctness/recPointFuel.wat 2 5` returned `7` and `8`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.recStatusExitFuel --out .lake/build/core-correctness/recStatusExitFuel.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke recStatusExitFuel .lake/build/core-correctness/recStatusExitFuel.wat 10 1` returned `1`, `0`, and `3`.
- [x] `node test/run_all.js` returned `checked 60 report classification cases`, `checked 369 accepted, 17 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Structured Nat-fuel recursion state

The existing Nat-fuel recursion path already flattened structured carried parameters through the same ABI machinery used for ordinary calls.  The new tests make that support explicit for a carried structure and a carried tagged value.  The loop update assigns each flattened carried slot through temporary locals, so multi-slot carried values update atomically with respect to later slot assignments in the same recursive step.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build`
- [x] `node test/report_classification.js` returned `checked 62 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 372 accepted, 17 rejected, and 7 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.recPointCarryFuel --out .lake/build/core-correctness/recPointCarryFuel.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime --invoke recPointCarryFuel .lake/build/core-correctness/recPointCarryFuel.wat 3 1 10` returned `4` and `16`.
- [x] `node test/run_all.js` returned `checked 62 report classification cases`, `checked 372 accepted, 17 rejected, and 7 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: ByteArray results and push

The generic compiler now accepts `ByteArray` results through the same pointer-length ABI used for `ByteArray` parameters.  Returned buffers may alias input memory or slices, or they may point to arena memory allocated by compiled code.  Hosts must read returned bytes before calling `reset`, because the arena owns the allocation lifetime and the compiler does not free individual byte buffers.

`ByteArray.empty` lowers to `(0, 0)`.  `ByteArray.push` evaluates the source and pushed byte, allocates `len + 1` bytes, copies the source bytes with byte loads and stores, and writes the appended byte.  The scalar length expression still forces the pushed value, so a trap in the byte expression is preserved even when source code asks only for the size of the pushed array.  `LeanExe.Examples.ByteArrayPrograms.tailSlice` covers a returned view into input memory rather than an owned arena allocation.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 42 bytearray allocation cases`.
- [x] `node test/core_correctness.js` returned `checked 374 accepted, 16 rejected, and 8 trapped cases`.
- [x] `.lake/build/bin/lean-wasm report --module LeanExe.Examples.ByteArrayPrograms --entry LeanExe.Examples.ByteArrayPrograms.appendBang` reported `entry shape: ByteArray -> ByteArray`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime --invoke bytesABC .lake/build/bytearray-programs/bytesABC.wasm` returned pointer `4099` and length `3`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/bytearray-programs/appendBang.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 64 report classification cases`, `checked 374 accepted, 16 rejected, and 8 trapped cases`, `checked 42 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: ByteArray append

The generic compiler now lowers `ByteArray.append` through a second byte-buffer allocation primitive.  The emitted code evaluates both inputs, allocates `left.size + right.size` bytes, copies the left bytes into the result, copies the right bytes after them, and returns the result pointer.  The length expression evaluates both operands, so a trap hidden in the construction of the right operand is still observed when source code asks only for the appended buffer's size.

`LeanExe.Examples.ByteArrayPrograms.appendABCXYZ` covers appending two compiler-constructed buffers.  `appendInputABC` covers appending a compiler-constructed suffix to host-provided input.  The memory harness reads the returned pointer-length pair and compares the result bytes.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 45 bytearray allocation cases`.
- [x] `node test/core_correctness.js` returned `checked 376 accepted, 16 rejected, and 9 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 66 report classification cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime --invoke appendABCXYZ .lake/build/bytearray-programs/appendABCXYZ.wasm` returned pointer `4108` and length `6`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/bytearray-programs/appendInputABC.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 66 report classification cases`, `checked 376 accepted, 16 rejected, and 9 trapped cases`, `checked 45 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: ByteArray set

The generic compiler now lowers proof-indexed `ByteArray.set`.  The emitted code evaluates the source, index, and replacement byte, checks the index before writing, allocates a fresh buffer with the original length, copies the source bytes, writes the replacement byte at the requested index, and returns the result pointer.  The length expression forces the index and replacement byte, so traps in those demanded expressions are preserved when source code asks only for the updated buffer's size.

`LeanExe.Examples.ByteArrayPrograms.setABC` covers a compiler-constructed buffer.  `setFirstBang` covers a host-provided input buffer and the empty-input branch where the proof-indexed update is not evaluated.  The operation remains proof-indexed; unchecked byte updates still need a separate source form and trap policy.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 49 bytearray allocation cases`.
- [x] `node test/core_correctness.js` returned `checked 378 accepted, 16 rejected, and 10 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 68 report classification cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime --invoke setABC .lake/build/bytearray-programs/setABC.wasm` returned pointer `4102` and length `3`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/bytearray-programs/setFirstBang.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 68 report classification cases`, `checked 378 accepted, 16 rejected, and 10 trapped cases`, `checked 49 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: ByteArray mk

The generic compiler now lowers `ByteArray.mk` for `Array UInt8`.  The emitted code evaluates the source array, reads its length header, allocates that many bytes, copies each `UInt8` cell into one byte of the new buffer, and returns the result pointer.  This gives byte literals a direct source form through `ByteArray.mk #[(65 : UInt8), ...]` rather than requiring a chain of `push` calls.

`LeanExe.Examples.ByteArrayPrograms.mkABC` covers the source form used by ordinary byte literals.  `LeanExe.Examples.Correctness.byteArrayMkSizeForcesArrayTrap` checks that asking for the size of the constructed byte array still evaluates the source array element.  The current support is monomorphic: the source array must be `Array UInt8`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 50 bytearray allocation cases`.
- [x] `node test/core_correctness.js` returned `checked 380 accepted, 16 rejected, and 11 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 69 report classification cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime --invoke mkABC .lake/build/bytearray-programs/mkABC.wasm` returned pointer `4224` and length `3`.
- [x] `node test/run_all.js` returned `checked 69 report classification cases`, `checked 380 accepted, 16 rejected, and 11 trapped cases`, `checked 50 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: ByteArray foldl

The generic compiler now lowers `ByteArray.foldl` for one-slot scalar accumulators.  The emitted code evaluates the buffer, start, stop, and initial accumulator, clamps stop to the buffer size, skips the body when the range is empty, and otherwise loops over bytes from left to right.  Each iteration loads one `UInt8`, evaluates the fold function body against the current accumulator and byte, stores the new accumulator, and advances the index.

`LeanExe.Examples.ByteArrayPrograms.foldSum` covers a full-buffer fold, and `foldWindowDecimal` covers an explicit start and stop range.  `LeanExe.Examples.Correctness.byteArrayFoldEmptySkipsFunctionTrap` checks that an empty range does not evaluate the fold body.  This adds a loop-like source form for byte processing without relying on the restricted Nat-fuel recursion pattern.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 56 bytearray allocation cases`.
- [x] `node test/core_correctness.js` returned `checked 383 accepted, 16 rejected, and 11 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 70 report classification cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/bytearray-programs/foldWindowDecimal.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 70 report classification cases`, `checked 383 accepted, 16 rejected, and 11 trapped cases`, `checked 56 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: ByteArray copySlice

The generic compiler now lowers value-level `ByteArray.copySlice`.  The implementation follows the Lean 4.29.1 definition in `Init/Data/ByteArray/Basic.lean`: it copies the destination prefix, a bounded source slice, and the destination suffix beginning after the bytes actually copied.  The `exact` argument affects capacity behavior in the runtime primitive, but the pure Lean definition does not use it to determine the resulting bytes, so extraction does not evaluate it.

`LeanExe.Examples.ByteArrayPrograms.copyInputMiddle` covers replacement inside an existing destination.  `copyInputPastDest` covers the case where `destOff` is beyond the destination size; the result appends the available source bytes without inserting padding.  `copyShortSource` checks that the suffix starts after the bytes copied, not after the requested length.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 63 bytearray allocation cases`.
- [x] `node test/core_correctness.js` returned `checked 387 accepted, 16 rejected, and 11 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 71 report classification cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/bytearray-programs/copyInputPastDest.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 71 report classification cases`, `checked 387 accepted, 16 rejected, and 11 trapped cases`, `checked 63 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Array foldl

The generic compiler now lowers `Array.foldl` for fixed-width arrays and one-slot accumulators.  This covers scalar arrays and arrays whose elements flatten to a fixed number of scalar slots, including monomorphic nonrecursive structures and small tagged values.  The emitted code evaluates the array, start, stop, and initial accumulator, clamps stop to the array size, loads each element into local slots, evaluates the fold body against the accumulator and current element, and stores the new accumulator.

`LeanExe.Examples.Correctness.arrayFoldSum` and `arrayFoldWindow` cover scalar arrays, including an explicit start and stop range.  `arrayFoldEmptySkipsFunctionTrap` checks that an empty range does not evaluate the fold body.  `arrayStructureFoldRead` covers a structured element loaded from a multi-slot array layout.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 391 accepted, 16 rejected, and 11 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 72 report classification cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/core-correctness/arrayStructureFoldRead.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 72 report classification cases`, `checked 391 accepted, 16 rejected, and 11 trapped cases`, `checked 63 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: ByteArray append notation

The extractor now lowers `HAppend.hAppend` when the checked result type is `ByteArray`.  The lowering reuses the same allocation and copy operation as `ByteArray.append`: it evaluates the left and right operands, allocates the combined byte length, copies the left bytes first, and copies the right bytes after them.  Non-`ByteArray` `HAppend.hAppend` applications still pass through the existing scalar extraction path, which preserves the prior array append-notation support.

`LeanExe.Examples.ByteArrayPrograms.appendNotationABCXYZ` covers ordinary `++` source syntax over byte arrays.  The report now classifies `HAppend.hAppend` as implemented for supported array and byte-array append notation.  The generated WAT for the new example validates under the local Wasmtime tool.

Checks run:

- [x] `lake build`
- [x] `node test/bytearray_alloc.js` returned `checked 64 bytearray allocation cases`.
- [x] `node test/core_correctness.js` returned `checked 391 accepted, 16 rejected, and 11 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 73 report classification cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/bytearray-programs/appendNotationABCXYZ.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 73 report classification cases`, `checked 391 accepted, 16 rejected, and 11 trapped cases`, `checked 64 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: ByteArray set!

The generic compiler now lowers trapping `ByteArray.set!`.  The operation uses the existing copy-on-write byte update lowering: it evaluates the source, index, and replacement byte, checks the index, allocates a fresh buffer with the original length, copies the source bytes, writes the replacement byte, and traps when the index is out of bounds.  This gives source code the ordinary non-proof update form while keeping alias behavior conservative.

`LeanExe.Examples.ByteArrayPrograms.setBangABC` covers a compiler-constructed buffer, and `setBangFirstQuestion` covers a host-provided buffer guarded by an empty check.  `LeanExe.Examples.Correctness.byteArraySetBangTrap` checks the out-of-bounds trap path.  The implementation does not add `USize` indexing or `ByteArray.uset`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 68 bytearray allocation cases`.
- [x] `node test/core_correctness.js` returned `checked 392 accepted, 16 rejected, and 12 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 74 report classification cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/bytearray-programs/setBangFirstQuestion.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 74 report classification cases`, `checked 392 accepted, 16 rejected, and 12 trapped cases`, `checked 68 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: ByteArray UInt64 decoding

The generic compiler now lowers `ByteArray.toUInt64LE!` and `ByteArray.toUInt64BE!` from Lean's `Init.Data.ByteArray.Extra` module.  The lowering checks that the byte-array length is exactly eight, then emits byte loads, left shifts, and bitwise-or operations to construct the `UInt64` result.  A wrong length traps in Wasm instead of calling Lean's panic runtime.

`LeanExe.Examples.ByteArrayPrograms.readUInt64LE` and `readUInt64BE` cover host-provided byte input.  `LeanExe.Examples.Correctness.byteArrayToUInt64LE` and `byteArrayToUInt64BE` cover compiler-constructed byte arrays, while `byteArrayToUInt64Trap` covers the size-check failure.  This adds a common binary-parser primitive without adding string or `IO` support.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 70 bytearray allocation cases`.
- [x] `node test/core_correctness.js` returned `checked 394 accepted, 16 rejected, and 13 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 75 report classification cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/bytearray-programs/readUInt64LE.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 75 report classification cases`, `checked 394 accepted, 16 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: ByteArray findIdx?

The generic compiler now lowers `ByteArray.findIdx?` for direct one-argument byte predicates returning `Bool`.  The emitted search scans bytes from left to right, returns `some index` at the first true predicate result, and returns `none` if the search reaches the end.  Empty search ranges do not evaluate the predicate.

`LeanExe.Examples.ByteArrayPrograms.findQuestion` and `findQuestionAfterFirst` cover host-provided byte input.  `LeanExe.Examples.Correctness.byteArrayFindIdxSome`, `byteArrayFindIdxNone`, `byteArrayFindIdxStart`, and `byteArrayFindIdxEmptySkipsPredicateTrap` cover returned `Option Nat` values and skipped predicate evaluation.  The current support requires the predicate to remain a direct lambda after elaboration; general closure values remain outside the subset.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/core_correctness.js` returned `checked 398 accepted, 16 rejected, and 13 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 76 report classification cases`.
- [x] `node test/bytearray_alloc.js` returned `checked 70 bytearray allocation cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/core-correctness/byteArrayFindIdxStart.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 76 report classification cases`, `checked 398 accepted, 16 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Array findIdx?

The generic compiler now lowers `Array.findIdx?` for fixed-width array element layouts and direct one-argument predicates returning `Bool`.  The emitted search loads each element into the same local slot representation used by `Array.map` and `Array.foldl`, checks the predicate, returns `some index` at the first true result, and returns `none` at the end of the array.  Empty arrays do not evaluate the predicate.

`LeanExe.Examples.Correctness.arrayFindIdxSome` and `arrayFindIdxNone` cover scalar arrays.  `arrayFindIdxStructure` covers a structure-array element, and `arrayFindIdxStatus` covers a tagged element with a predicate that matches on the source-defined inductive.  `arrayFindIdxEmptySkipsPredicateTrap` checks skipped predicate evaluation.  The current support requires a direct lambda predicate and does not compile escaped predicate values.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 403 accepted, 16 rejected, and 13 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 77 report classification cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/core-correctness/arrayFindIdxStatus.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 77 report classification cases`, `checked 403 accepted, 16 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Array any and all

The generic compiler now lowers `Array.any` and `Array.all` for fixed-width array element layouts and direct one-argument predicates returning `Bool`.  The lowering clamps `stop` to the array size, starts at `start`, and short-circuits on the first decisive result.  Empty ranges return `false` for `any` and `true` for `all` without evaluating the predicate.

`LeanExe.Examples.Correctness.arrayAnySome`, `arrayAnyWindowFalse`, `arrayAllScalars`, and `arrayAllWindowTrue` cover scalar arrays and explicit ranges.  `arrayAllStructure` covers structure elements, and `arrayAnyStatus` covers tagged elements with a predicate that matches on a source-defined inductive.  `arrayAnyEmptySkipsPredicateTrap` and `arrayAllEmptySkipsPredicateTrap` check skipped predicate evaluation.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 411 accepted, 16 rejected, and 13 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 78 report classification cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/core-correctness/arrayAllStructure.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 78 report classification cases`, `checked 411 accepted, 16 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Array find?

The generic compiler now lowers `Array.find?` for fixed-width array element layouts and direct one-argument predicates returning `Bool`.  The operation returns a source-shaped `Option` payload, so scalar, structure, and tagged elements all use the existing `Option` ABI and internal representation.  The current lowering emits one search for the tag and one search for each demanded payload slot; this preserves pure results but should be replaced by a shared loop result before treating `find?` as a performance primitive.

`LeanExe.Examples.Correctness.arrayFindSome` and `arrayFindNone` cover scalar payloads.  `arrayFindStructure` covers a returned structure payload, and `arrayFindStatus` covers a returned tagged payload.  `arrayFindEmptySkipsPredicateTrap` checks skipped predicate evaluation on an empty array.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 416 accepted, 16 rejected, and 13 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 79 report classification cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/core-correctness/arrayFindStatus.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 79 report classification cases`, `checked 416 accepted, 16 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Array filter

The generic compiler now lowers `Array.filter` for fixed-width array element layouts and direct one-argument predicates returning `Bool`.  The emitted code clamps `stop` to the source size, scans the selected range from left to right, copies matching element slots into a new arena array, and writes the matched count into the result header.  The arena reservation uses the source length as capacity, so the allocated region can exceed the observable result length.

`LeanExe.Examples.Correctness.arrayFilterScalarsRead`, `arrayFilterWindowRead`, and `arrayFilterNoneSize` cover scalar arrays, explicit ranges, and empty results.  `arrayFilterStructureRead` covers filtered structure elements, and `arrayFilterStatusRead` covers filtered tagged elements.  `arrayFilterEmptySkipsPredicateTrap` checks skipped predicate evaluation for an empty source.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 422 accepted, 16 rejected, and 13 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 80 report classification cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/core-correctness/arrayFilterStructureRead.wat` accepted the generated module.
- [x] `node test/run_all.js` returned `checked 80 report classification cases`, `checked 422 accepted, 16 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: Internal recursive inductives

The extractor now accepts monomorphic self-recursive user-defined inductives as internal values.  `Ty.recVariant` marks a recursive source type, and `ExtractedValue.recursiveVariant` keeps freshly constructed values lazy until a pointer is required.  When the value crosses a strict boundary, the extractor materializes it into the arena as a fixed-slot object: slot `0` stores the constructor tag, and later slots store flattened payloads for every constructor in declaration order.  Recursive fields store one pointer slot.  Matches over materialized values load the tag and demanded fields from the object, while matches over fresh constructor values use the existing lazy payload path.

`LeanExe.Examples.Correctness.U64List` covers construction, nested matching, branch-selected recursive values, and a fuel-recursive traversal that carries the list pointer through the existing `Nat`-fuel loop form.  Public recursive values remain outside the Wasm ABI: `rejectRecursiveInductiveParam` and `rejectRecursiveInductiveReturn` check that entry parameters and results of recursive inductive type are rejected.  The implementation does not handle mutual recursion, polymorphic recursive types, arrays of recursive values, recursive structures, or a garbage collector.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 429 accepted, 18 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 80 report classification cases`, `checked 429 accepted, 18 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-11: ASCII string library

`LeanExe.AsciiString` is a one-field structure over `ByteArray`, with explicit checked and trusted constructors.  The checked path uses a fuel-recursive byte scan and returns `Option AsciiString`; the trusted path wraps a byte buffer without validation.  The representation keeps the WASM ABI unchanged, because an ASCII string flattens to the pointer-length pair of its `ByteArray` field.

`LeanExe.Examples.AsciiStringPrograms` covers ASCII validation, checked conversion, checked byte push, trusted append, extraction, and returned byte output.  The test harness compiles those examples through the generic compiler and compares WASM results with expected bytes.  The current library intentionally avoids Lean `String` and Unicode semantics; it is byte-oriented text for parsers and generators that need ASCII syntax.

Checks run:

- [x] `lake build LeanExe.Examples.AsciiStringPrograms`
- [x] `node test/asciistring.js` returned `checked 14 asciistring cases`.
- [x] `node test/report_classification.js` returned `checked 85 report classification cases`.
- [x] `node test/run_all.js` returned `checked 85 report classification cases`, `checked 429 accepted, 18 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, and `checked 56 cases`.

## 2026-05-11: Schema-specific JSON over ASCII

`LeanExe.Examples.JsonDouble.transform` is the first JSON-shaped example.  It accepts a `ByteArray`, validates it as `AsciiString`, parses the exact object shape `{ "n" : digits }`, doubles the parsed `UInt64` when the result fits, and returns generated JSON bytes.  It returns `{"error":1}` for malformed input, non-ASCII input, parse overflow, and doubled-value overflow.

The compiler change adds a value-level call binding for helper calls that return structured values.  A direct call now stores all flattened result slots in locals and reconstructs the source value shape, so callers can match an `Option` result or project a structure returned by a bounded recursive helper.  `recPointFuelCallRead` covers this path independently of the JSON example, and the JSON parser exercises an `Option ParsedNumber` result from a recursive decimal parser.

The JSON support remains deliberately schema-specific.  It has no general JSON AST, no string escape parser, no arrays, no object field search, and no Unicode handling.  Those belong in later library work once the accepted subset has enough text and recursive data support to make a general parser useful.

Checks run:

- [x] `lake build LeanExe.Examples.JsonDouble`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/json_double.js` returned `checked 12 json double cases`.
- [x] `node test/report_classification.js` returned `checked 87 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 430 accepted, 18 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 87 report classification cases`, `checked 430 accepted, 18 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, `checked 12 json double cases`, and `checked 56 cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/json-double/transform.wat` accepted the generated module.

## 2026-05-11: Reusable ASCII JSON helpers

The JSON examples now share small helper modules instead of carrying local byte parsers in each example.  `LeanExe.Ascii.Basic` contains byte constants, whitespace scanning, and byte expectations; `LeanExe.Ascii.Decimal` contains checked unsigned decimal parsing and rendering for `UInt64`; `LeanExe.Ascii.Json` contains one-byte field-name parsing and the shared `{"error":1}` result.  `JsonDouble` now uses those helpers, and `JsonAdd` demonstrates a fixed two-field object that returns a checked `UInt64` sum.

The compiler now emits a direct WASM call for a nonrecursive helper with a one-slot scalar result when demand analysis proves that strict argument evaluation preserves Lean behavior.  The first version allowed structured direct calls without enough proof, which forced inactive `Option` payloads across the flattened result ABI and made `AsciiString.getD` trap on out-of-bounds input.  Structured helper returns still work, but nonrecursive structured helpers remain inlined unless the current recursive call machinery or an accepted call shape requires flattened result slots.

Checks run:

- [x] `lake build`
- [x] `node test/json_double.js` returned `checked 22 json program cases`.
- [x] `node test/report_classification.js` returned `checked 88 report classification cases`.
- [x] `node test/run_all.js` returned `checked 88 report classification cases`, `checked 430 accepted, 18 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, `checked 22 json program cases`, and `checked 56 cases`.

## 2026-05-11: JSON Collatz length example

`LeanExe.Examples.JsonCollatzLength.transform` accepts a JSON-shaped `ByteArray` request of the form `{ "collatzLengthFor" : digits }` and returns `{"length":N}`.  The length counts terms, so `{"collatzLengthFor":41}` returns `{"length":110}`.  The program uses a checked Collatz length helper that rejects zero, decimal parse overflow, `3n+1` overflow under `UInt64`, and failure to reach `1` before the existing `maxSteps` fuel limit.

The JSON helper layer now has `expectBytes` and `expectFieldName` for fixed byte-string field names.  `expectBytesFuel` had to follow the accepted single-branch tail-recursive shape; an earlier nested-`if` loop was valid Lean but outside the current recursion recognizer.

Checks run:

- [x] `lake build`
- [x] `node test/json_double.js` returned `checked 31 json program cases`.
- [x] `node test/report_classification.js` returned `checked 89 report classification cases`.
- [x] `node test/run_all.js` returned `checked 89 report classification cases`, `checked 430 accepted, 18 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, `checked 31 json program cases`, and `checked 56 cases`.

## 2026-05-11: ASCII string literals for ByteArray

The extractor now lowers `String.toUTF8` when the receiver is a compile-time ASCII string literal.  The accepted source form is standard Lean syntax such as `"collatzLengthFor".toUTF8`, and the lowered value uses the same byte-buffer representation as `ByteArray.mk`.  Runtime `String` values remain unsupported: `String` parameters, `String` results, nonliteral receivers, non-ASCII literals, indexing, decoding, and general string operations are rejected.

The JSON examples now use string literals for fixed output prefixes and field names.  `LeanExe.Examples.Correctness.byteArrayStringLiteralReturn` and `byteArrayStringLiteralSize` cover accepted byte output and size queries, while `rejectRuntimeStringToUTF8` covers rejection of a nonliteral string receiver.

Checks run:

- [x] `lake build`
- [x] `node test/core_correctness.js` returned `checked 432 accepted, 19 rejected, and 13 trapped cases`.
- [x] `node test/json_double.js` returned `checked 31 json program cases`.
- [x] `node test/report_classification.js` returned `checked 89 report classification cases`.
- [x] `node test/run_all.js` returned `checked 89 report classification cases`, `checked 432 accepted, 19 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, `checked 31 json program cases`, and `checked 56 cases`.

## 2026-05-11: Internal arrays of recursive values

The compiler now treats a recursive inductive value as a one-slot array element when the array stays inside compiled Lean code.  The slot holds the heap pointer used for materialized recursive values.  This admits internal values such as `Array U64List` and recursive constructors that contain `Array U64Tree`.  Entry parameters and entry results whose array element layout contains a recursive value remain rejected.

The extractor changes stay narrow.  `arrayElementSlots?` now assigns one slot to `Ty.recVariant`, array element flattening materializes fresh recursive constructor values to heap pointers, and array load, find, and loop-local binding rebuild `ExtractedValue.heapVariant` from the stored pointer.  Recursive field type analysis now recognizes `Array self` structurally, avoiding recursive-layout rediscovery while checking constructors such as `U64Tree.node : Array U64Tree -> U64Tree`.  Direct helper calls now flatten arguments and non-exported results with the internal value flattener, so internal arrays of recursive values can pass through ordinary local helpers without becoming part of the public ABI.

`LeanExe.Examples.Correctness` covers recursive arrays through literals, `push`, `set!`, `map`, `foldl`, safe indexing, and a recursive inductive constructor that stores `Array U64Tree`.  The accepted cases exercise both fresh constructor values and recursive pointers loaded back from array storage.  The rejected cases cover public ABI rejection for `Array U64List` parameters and results.

Checks run:

- [x] `lake build`
- [x] `node test/core_correctness.js` returned `checked 437 accepted, 21 rejected, and 13 trapped cases`.
- [x] `node test/report_classification.js` returned `checked 90 report classification cases`.
- [x] `node test/run_all.js` returned `checked 90 report classification cases`, `checked 437 accepted, 21 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, `checked 31 json program cases`, and `checked 56 cases`.

## 2026-05-11: Limited JSON field tools

`LeanExe.Ascii.Json` now has reusable ASCII-only field lookup and object generation helpers.  `findFieldRange` scans a top-level object for a named field, and the typed getters read `UInt64`, restricted unescaped ASCII strings, booleans, null, nested object slices, nested array slices, or raw value slices from that range.  The value skipper handles unknown nested object and array values by tracking nesting depth and restricted strings, which supports practical field lookup without claiming full JSON grammar validation.

The generator side now has quoted-string helpers, field-prefix helpers, typed field appenders, and one-field object constructors for `UInt64`, `Bool`, and restricted ASCII strings.  The string grammar remains intentionally small: bytes must be ASCII, at least `32`, and neither quote nor backslash.  `appendRawField?` accepts a raw value only when the same limited value skipper consumes the whole slice after whitespace.

`LeanExe.Examples.JsonTools.transform` demonstrates byte-output generation through a direct one-field parse, and `LeanExe.Examples.JsonTools.lookup` demonstrates generic lookup across a skipped nested object as a scalar entry.  The split records a compiler limitation found during this work: a `ByteArray`-returning function that demands an `Option UInt64` payload found after a skipped field can trap in WASM even though the scalar lookup itself is correct.  That points at structured-value lowering around `Option` matches feeding byte-array output, not at the source JSON helper.

Checks run:

- [x] `lake build`
- [x] `node test/json_double.js` returned `checked 45 json program cases`.
- [x] `node test/report_classification.js` returned `checked 92 report classification cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 437 accepted, 21 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, `checked 45 json program cases`, and `checked 56 cases`.

## 2026-05-11: Collatz JSON output uses the helper layer

`LeanExe.Examples.JsonCollatzLength.resultJson` now emits its success object through `Ascii.Json.object1UInt64` instead of hand-building the prefix and appending the decimal digits.  The input parser remains the exact one-field parser.  Replacing that parser with `Ascii.Json.getUInt64Field` makes the generated byte-output function enormous under the current inlining strategy; the Node-based test harness refused to instantiate that function because of its per-function size.  The root cause is the compiler's handling of structured helper returns, so generic field lookup should wait for that compiler fix before it becomes the byte-output Collatz path.

## 2026-05-11: Structured helper calls and result materialization

The compiler now emits real WASM calls for accepted structured helper returns when strict argument evaluation is valid.  The IR has statement-level multi-result calls, so a helper returning `Option`, a structure, a tagged value, or a `ByteArray` stores its flattened result slots once before later projections or matches consume them.  The prior expression-only lowering copied a structured call into each demanded slot, which made the generic JSON Collatz example expand into hundreds of megabytes of WAT.

Conditional structured results now materialize through statement-level branches into result locals.  This preserves source-level branch selection for helpers that allocate or can trap, and it prevents a `ByteArray` result from calling the same branch once for the pointer and again for the length.  Safe array and byte-array indexing also guard inactive `Option` payloads, so a `none` result no longer performs the out-of-bounds payload read that Lean source code would skip.

`LeanExe.Examples.JsonCollatzLength.parseObject` now uses `Ascii.Json.getUInt64Field`, and the success output still uses `Ascii.Json.object1UInt64`.  The generated Collatz JSON module is `238332` bytes of WAT and `22735` bytes of WASM; the largest emitted function is `1580` WAT lines.  Wasmtime accepts the emitted WAT, and the full test suite reports `checked 437 accepted, 21 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, `checked 45 json program cases`, and `checked 56 cases`.

Checks run:

- [x] `lake build`
- [x] `node test/json_double.js` returned `checked 45 json program cases`.
- [x] `node test/report_classification.js` returned `checked 92 report classification cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 437 accepted, 21 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, `checked 45 json program cases`, and `checked 56 cases`.

## 2026-05-11: Strict structured materialization sites

Strict helper-call arguments now materialize top-level `let` and direct-call values before flattening argument slots.  The implementation binds each flattened argument slot to locals in source argument order before the call, so later structured helper arguments cannot run before earlier scalar expressions.  A structured helper result passed to another helper is therefore evaluated once, and recursive loop argument updates run any required structured calls before assigning carried slots.  The change keeps strict-call demand analysis in charge of whether a call may be emitted.

Eager fixed-width array element operations use the same materialization step for literal items, singleton values, pushed values, proof-indexed inserts and sets, and bang inserts and sets under their in-bounds branch.  For updates with array and index operands, the extractor binds those operands before running materialized element lets.  Guarded operations that define skipped-value behavior, including `setIfInBounds`, `insertIdxIfInBounds`, `modify`, `swapAt` projections, and `map` bodies, still keep value expressions inside the guarded or per-element expression.  Moving those expressions to an outer statement would force source expressions that Lean code can leave unevaluated.

`LeanExe.Examples.JsonTools.transform` now reads `n` through `Ascii.Json.getUInt64Field`, matching the scalar lookup example and accepting unknown skipped values before the requested field.  The JSON harness includes a one-megabyte WAT size guard for `JsonCollatzLength.transform`; the current generated WAT is `257071` bytes.  The core correctness corpus adds cases for structured helper results as call arguments, structured helper results stored as array elements, inactive structured safe-index payloads, and branch-selected `ByteArray` helper results.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 442 accepted, 21 rejected, and 13 trapped cases`.
- [x] `node test/json_double.js` returned `checked 46 json program cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 442 accepted, 21 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, `checked 46 json program cases`, and `checked 56 cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/json-programs/JsonCollatzLength-transform.wat`

## 2026-05-11: Strict materialization regressions and size guards

The extractor now names the strict-boundary helpers as `StrictSlots`, `StrictArgs`, `materializeStrictInternalSlots`, and `materializeStrictArrayElementSlots`.  This keeps the statement-like path separate from lazy expression flattening.  `Array.replicate` now uses the strict array-element path too, binding the count expression before running materialized element lets.

The correctness corpus adds guarded helper regressions for `insertIdxIfInBounds`, `setIfInBounds`, and empty `map` over structured arrays.  Each case passes a helper whose payload traps if evaluated, so moving a structured value out of a skipped branch would fail.  `arrayStructureReplicateHelperRead` covers the strict eager replicate path, and `core_correctness.js` adds a WAT size guard for that example.

The JSON harness now guards `JsonTools.transform` as well as `JsonCollatzLength.transform`.  Current guarded WAT sizes are `257071` bytes for `JsonCollatzLength.transform`, `229962` bytes for `JsonTools.transform`, and `9468` bytes for `arrayStructureReplicateHelperRead`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 446 accepted, 21 rejected, and 13 trapped cases`.
- [x] `node test/json_double.js` returned `checked 46 json program cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 446 accepted, 21 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, `checked 46 json program cases`, and `checked 56 cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/json-programs/JsonCollatzLength-transform.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/json-programs/JsonTools-transform.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache build/tools/wasmtime/current/wasmtime wast .lake/build/core-correctness/arrayStructureReplicateHelperRead.wat`

## 2026-05-11: Recursive step let bindings

The Nat-fuel recursion recognizer now accepts local `let` bindings at the start of the successor branch before the tail call or before the immediate `if` that selects between an early exit and the tail call.  This supports ordinary state-staging code such as computing the next accumulator value once, naming it, and then passing it to the next iteration or testing it for early exit.  The recognizer tracks the shifted recursive handle under each Lean `.letE`, so a recursive call under one or more lets still points at the generated `Nat.brecOn` handle rather than at the newest local binding.

Condition extraction now treats local `let` bindings as lazy condition-local bindings, matching value extraction and scalar expression extraction.  The prior path routed a let-bound proposition condition through scalar expression extraction, which rejected Lean's `Eq` proposition in a condition such as `let next := acc + 1; if next == 3 then ...`.  The corrected path preserves unused-let laziness: a step-local binding that would trap if evaluated remains skipped when the recursive step body does not demand it.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 449 accepted, 21 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 449 accepted, 21 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-11: List-shaped structural recursion

The extractor now lowers a narrow structural-recursion shape for supported self-recursive inductives.  The accepted helper has one parameter of the recursive inductive type, and each constructor may expose at most one direct self-recursive field.  The lowering recognizes Lean's generated `brecOn` form, matches on the heap tag, binds constructor fields from the heap object, and turns the generated `PProd.fst` below projection into a direct recursive WASM call on the recursive field.

This admitted ordinary list traversals without an explicit fuel parameter.  `LeanExe.Examples.Correctness.u64ListStructuralSum` summed `U64List` through direct structural recursion and was called from the public zero-argument demo.  At that checkpoint, `rejectStructuralBinarySize` used a binary recursive constructor with two direct recursive fields and was rejected with `structural recursion over multiple recursive fields is unsupported`; the later branching structural recursion entry supersedes that limitation.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 450 accepted, 22 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 450 accepted, 22 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-11: Parser state fixture

`LeanExe.Examples.Correctness.DigitState` is a small parser-state structure with a byte cursor and `UInt64` accumulator.  `digitStateParseFuel` carries that state through the accepted Nat-fuel loop shape, uses a helper to test whether the current byte is an ASCII digit, and uses a helper to advance the cursor and add the digit value.  The examples cover an all-digit input and an input that stops at a non-digit byte.

This slice did not require a compiler change.  It records that the current subset already supports a common parser style: a `ByteArray` input, a cursor-state structure, helper calls for predicate and step logic, and a bounded state-passing loop.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 452 accepted, 22 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 452 accepted, 22 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 14 asciistring cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-11: ASCII string comparison utilities

`AsciiString` now includes `equals`, `startsWith`, and `containsByte`.  The implementations use the accepted Nat-fuel tail-recursive loop shape with explicit accumulator state rather than nested recursive branches, so they compile through the current recursion recognizer.  The example module exposes these utilities through byte-array entry points that validate ASCII input before constructing `AsciiString` values.

Checks run:

- [x] `lake build LeanExe.Examples.AsciiStringPrograms`
- [x] `node test/asciistring.js` returned `checked 22 asciistring cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 452 accepted, 22 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 22 asciistring cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-11: Structure-backed integer map

`LeanExe.Examples.IntMap` now represents each hash-table cell as a `Slot` structure and the table as a `Table` structure over `Array Slot`.  The example still uses a fixed capacity of `256`, open addressing, key `0` as the empty marker, and keys `1` through `100` mapped to `k * 10 + 7`.  This updates the old raw adjacent-word array example to current subset style.

The new `test/intmap.js` regression compiles `checksum` and `query` and runs them under the checked-in Wasmtime binary.  It checks the aggregate checksum and lookups for the first inserted key, last inserted key, and a missing key.

Checks run:

- [x] `lake build LeanExe.Examples.IntMap`
- [x] `node test/intmap.js` returned `checked 4 intmap cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 452 accepted, 22 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 22 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Pure for loops over bytes and arrays

The extractor now recognizes Lean's generated `ForIn.forIn` form when the monad is `Id`, the collection is `ByteArray` or a fixed-width `Array`, and the accumulator has a supported one-slot type.  The lowering extracts the yielded accumulator from a `ForInStep.yield` body and emits the existing byte-array or array fold IR.  It preserves the generated `PUnit` bind as a local let while parsing the yield expression, because the yielded value's de Bruijn indices refer through that binder.

`LeanExe.Examples.Correctness.idRunByteArrayForSum` and `idRunArrayForSum` cover the accepted source form with `let mut` accumulator syntax.  `rejectIdForLoop` remains rejected for `Std.Legacy.Range`, now with a precise unsupported collection-type diagnostic.  `ForInStep.done`, `break`, effects, range loops, polymorphic iterators, and multi-slot accumulators remain outside this slice.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 454 accepted, 22 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 454 accepted, 22 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 22 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Monomorphic recursive instances

The recursive-inductive type representation now records concrete runtime type parameters.  This lets the extractor treat `List UInt64` as a specialized recursive inductive instance rather than as an unsupported polymorphic value.  Constructor extraction splits constructor type parameters from runtime fields, instantiates constructor field domains with the concrete parameter types, and then reuses the existing heap-recursive constructor, matcher, and structural-recursion machinery.

This is not a `List` primitive.  `LeanExe.Examples.Correctness.leanListHeadDemo`, `leanListTailHeadDemo`, and `leanListStructuralSumDemo` use ordinary Lean `List UInt64` literals, pattern matching, helper calls, and direct structural recursion.  Standard `List` library calls such as `map`, `filter`, `foldl`, `any`, `find?`, `concat`, and append still need higher-order specialization or first-order library extraction before they can compile.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 457 accepted, 22 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 457 accepted, 22 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 22 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Direct-lambda List library specialization

Transparent specialization now unfolds nonlocal transparent applications when the application contains a direct lambda argument and the callee is outside the primitive, recursor, and matcher families that the extractor already lowers explicitly.  The purpose is to reduce ordinary library code to the same first-order terms the compiler already accepts, without adding a `List` primitive or a hidden runtime path.  The matcher parser now locates the instantiated scrutinee argument in generated matcher types, which handles polymorphic matchers produced by specialized `List UInt64` library calls.

This slice accepts `LeanExe.Examples.Correctness.leanListMapDemo`, `leanListFilterDemo`, `leanListFindDemo`, and `leanListFindMissingDemo`.  `List.map`, `List.filter`, and `List.find?` compile here because the direct lambdas specialize away and the resulting structural recursion returns first-order data.  At this checkpoint, closed `List.foldl` and direct `List.any` examples still failed because their lowered definitions returned function values from structural recursion.

`List.map` exposed a recursive-value laziness bug in structured branch selection.  `valueIte` previously combined recursive-variant payloads from both branches, which forced inactive recursive constructor payloads and could make a finite list traversal diverge.  Recursive variant branch values now stay behind an `ite` wrapper, so inactive constructor payloads are not evaluated during materialization.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 461 accepted, 24 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 461 accepted, 24 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 22 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Function-valued structural recursion

The structural-recursion extractor now handles generated motives that return function values when those functions can be removed during extraction.  Direct-lambda post arguments are substituted into the generated branch body, and first-order carried post arguments are mapped to explicit helper parameters after the recursive-inductive parameter.  Recursive calls through the generated `PProd.fst` projection now accept the same post arguments, filtering out direct lambdas and passing only first-order carried values to the compiled helper.

The generated matcher parser now chooses the recursive-inductive scrutinee instead of the first supported typed matcher argument, and it treats the final constructor-count arguments after the scrutinee as the branch arms.  This handles both `List.foldl.match_1`, where the accumulator argument precedes the scrutinee, and `List.any.match_1`, where the predicate argument follows the scrutinee.  Constructor detection in generated arm types now searches motive arguments, which covers arm types such as `motive [] p` and preserves the existing nullary-constructor `Unit` binder form.

`LeanExe.Examples.Correctness.leanListFoldlDemo` uses ordinary `List.foldl` over `List UInt64` with a noncommutative decimal accumulator, so the test catches binder-order mistakes.  `leanListAnyDemo` and `leanListAnyMissingDemo` use ordinary `List.any` with direct-lambda predicates.  Direct closed `List.foldl` remains rejected in `rejectLeanListFoldlClosedDemo`, because its initial accumulator would require a hidden carried parameter that the current source-to-WASM function ABI does not synthesize.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 464 accepted, 24 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 464 accepted, 24 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 22 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Compile-time ASCII String expressions

The extractor now treats Lean `String` as a compile-time-only source convenience rather than a supported runtime structure.  `String` is explicitly excluded from the generic structure classifier, so `String` parameters, results, and helper-call ABI slots remain rejected.  Accepted string expressions are ASCII literals, local `String` lets, top-level `String` constants, `String.append`, and append notation through `++`, when the expression is consumed by `String.toUTF8`, `String.length`, `String.isEmpty`, `==`, or `!=`.

This slice deliberately stopped short of an `AsciiString.ofString` helper.  A direct helper with a `String` parameter tempts the generic function path to treat source strings as runtime values, which is the wrong boundary for the current compiler.  Fixed protocol text should use `"field".toUTF8` for `ByteArray` values, and runtime text should enter as `ByteArray` followed by `AsciiString.ofByteArray?` validation.

Checks run:

- [x] `lake build lean-wasm LeanExe.Examples.Correctness LeanExe.Examples.AsciiStringPrograms LeanExe.Examples.JsonCollatzLength LeanExe.Examples.JsonTools`
- [x] `node test/asciistring.js` returned `checked 23 asciistring cases`.
- [x] `node test/core_correctness.js` returned `checked 471 accepted, 26 rejected, and 13 trapped cases`.
- [x] `node test/json_double.js` returned `checked 46 json program cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 471 accepted, 26 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Multi-slot pure for-loop accumulators

Pure `Id.run` `for` loops over `ByteArray` and fixed-width `Array` now carry accumulator values with the normal internal slot layout rather than the previous scalar-only shape.  The extractor reconstructs the accumulator from loop-local slots, extracts the yielded value as a structured value, flattens the body result, and uses multi-slot fold IR whose body stages all result slots before copying them back to the accumulator slots.  The accepted accumulator types include scalars, `Array` pointer values, products, structures, nonrecursive tagged values, and recursive-inductive pointer values, while accumulator shapes containing `ByteArray` remain rejected because pointer and length must be produced atomically.

The binary and WAT emitters gained matching `arrayFoldMultiSlot` and `byteArrayFoldMultiSlot` expression forms for projected slots, plus statement forms that materialize a full structured loop result once into result locals.  Body slots are staged through temporary locals so updates do not observe earlier field writes from the same iteration.  The correctness corpus now covers a `ByteArray` scan carrying a `DigitState` structure, an array scan carrying a `Status` tagged value, and the explicit rejection of a `ByteArray` accumulator.

Checks run:

- [x] `lake build`
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 474 accepted, 27 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Pure range for loops

Pure `Id.run` `for` loops now accept `Std.Legacy.Range` collections in addition to `ByteArray` and fixed-width `Array`.  The extractor reads the checked range structure fields for start, stop, and step, binds the current index as a bounded `Nat`, and reuses the same multi-slot accumulator path used by byte and array loops.  The emitted loop uses exclusive-stop order and checked bounded-`Nat` addition for the index increment.

The IR gained `rangeFoldMultiSlot` expression and statement forms.  The statement form materializes a full structured range-loop result once into result locals, while the expression form covers projected loop results.  The correctness corpus now covers a simple count loop, a stepped range sum, a structured `DigitState` range accumulator, and rejection of a `ByteArray` accumulator in a range loop.

Checks run:

- [x] `lake build`
- [x] `node test/core_correctness.js` returned `checked 477 accepted, 27 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 477 accepted, 27 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Early-exit pure for loops

Pure `Id.run` `for` loops now retain both parts of the elaborated `ForInStep`: the next accumulator value and the step-completion flag.  The extractor accepts `ForInStep.yield`, `ForInStep.done`, pure wrapping, the generated `PUnit` bind shape used by mutable assignments, and step-level `if` expressions whose branches both produce supported `ForInStep` values.  The correctness corpus covers ordinary `break` in accepted `ByteArray`, fixed-width-array, and range loops without adding a special source-level `break` case to the compiler.

The multi-slot fold IR now carries a `bodyDone` expression.  The binary and WAT emitters evaluate the next accumulator slots into temporary locals, evaluate the done flag before copying those temporaries back to the accumulator slots, copy the accumulator, and branch out of the loop when the flag is true.  Evaluating the done flag before the copy preserves the source view of the old accumulator and current item while still returning the done value as the final accumulator.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 481 accepted, 27 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 481 accepted, 27 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Continue in pure for loops

Source-level `continue` now compiles in accepted pure `Id.run` `for` loops.  Lean elaborates `continue` to `ForInStep.yield` with the current accumulator, so the existing `ForInStep` parser covers explicit `else` branches.  The no-`else` source form introduces a local joinpoint for the remaining statements in the loop body; the parser now beta-reduces direct lambda joinpoints before parsing the step so code such as `if cond then continue; acc := ...` and `if cond then break; acc := ...` compiles without a compiler-specific source rewrite.

The correctness corpus covers `continue` over `ByteArray`, fixed-width `Array`, and `Std.Legacy.Range`, plus a structured range accumulator.  It also covers a no-`else` `break` before a later assignment, which uses the same joinpoint lowering.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 486 accepted, 27 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 486 accepted, 27 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Recursive array descent

The extractor now preserves `WellFounded.fix` during local beta specialization, because Lean uses that generated form for recursive descent through an `Array` field.  The new lowering handles the checked shape produced by a recursive function over a tree whose constructor contains `Array self`: the matcher scrutinee is the original function parameter, constructor arms bind the generated well-founded recursive handle, and recursive calls through that handle lower to ordinary WASM self-calls.  `Array.foldl` now recognizes the generated `Array.attach` and `Array.map_unattach.match_1` wrapper, extracting the fold over the underlying array while erasing membership proofs and preserving the callback binder order.

The feature is narrow and recognizes only Lean's generated array-child traversal shape.  The accepted source must be first-order and monomorphic.  Arbitrary `WellFounded.fix`, recursive public ABI values, mutual recursion, and course-of-values traversal through generated below tails remain outside the accepted language.

Checks run:

- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.u64TreeSizeDemo --out /tmp/u64TreeSizeDemo.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke u64TreeSizeDemo /tmp/u64TreeSizeDemo.wasm` returned `6`.
- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 487 accepted, 27 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 487 accepted, 27 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Branching structural recursion

Structural-recursion lowering now represents Lean's generated below value as a small projection tree instead of a single recursive handle.  A direct recursive field contributes a pair whose first projection is the recursive result for that field, and branching constructors combine those field pairs with the same right-nested `PProd` shape generated by Lean.  Projection paths such as `x.1.1` and `x.2.1` now lower to separate WASM self-calls on the selected recursive field, while projection into the generated below tail remains rejected as unsupported course-of-values recursion.

`LeanExe.Examples.Correctness.u64BinaryStructuralSizeDemo` covers a binary tree with two direct recursive fields in one constructor.  `LeanExe.Examples.Correctness.u64ExprEvalDemo` covers an expression AST with `lit`, `add`, and `mul`, so the branch-recursion path now supports a representative evaluator shape.

Checks run:

- [x] `lake build lean-wasm LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 489 accepted, 26 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 489 accepted, 26 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke u64BinaryStructuralSizeDemo /tmp/u64BinaryStructuralSizeDemo.wasm` returned `3`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke u64ExprEvalDemo /tmp/u64ExprEvalDemo.wasm` returned `45`.

## 2026-05-12: Closed structural folds

The extractor now lowers a top-level closed structural fold over a list-shaped recursive inductive.  The accepted shape is Lean's generated `brecOn` body with one hidden first-order accumulator, one constructor with a single direct recursive field, and terminal constructors whose arms return the accumulator.  The recursive constructor arm must tail-call the generated below projection for that direct recursive field with the next accumulator value, which gives the compiler a loop over the heap pointer and accumulator slots instead of a synthesized helper function.

This admits direct source such as `leanList123.foldl (fun acc x => acc * 10 + x) 0`.  The lowering is still shape-based rather than a `List` primitive: the code checks the recursive-inductive layout, the generated matcher, the terminal arms, and the recursive-field tail call.  Nested closed structural folds, closed `List.any`, general function-valued motives, and hidden carried arguments outside this one-accumulator fold form remain outside the accepted language.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListFoldlClosedDemo --out /tmp/leanListFoldlClosedDemo.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListFoldlClosedDemo /tmp/leanListFoldlClosedDemo.wasm` returned `123`.
- [x] `node test/core_correctness.js` returned `checked 490 accepted, 25 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 490 accepted, 25 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Closed structural predicates

The extractor now lowers closed structural predicate bodies over list-shaped recursive inductives.  The accepted shape is Lean's generated `brecOn` body with one direct-lambda predicate, one constructor with a single direct recursive field, and terminal constructors that return the predicate identity value.  The recursive constructor arm must combine the predicate result for the current fields with the generated recursive-field result through `Bool.or` for existential predicates or `Bool.and` for universal predicates.

The IR gained `heapLinearPredicate`, which emits a heap-pointer loop with short-circuit behavior.  This remains a structural-recursion lowering rather than a `List` primitive: the extractor checks the recursive-inductive layout, generated matcher, terminal values, predicate lambda, and recursive-field projection before emitting the loop.  The current tests cover direct `List.any` and `List.all` over `List UInt64`, including both short-circuit and terminal cases.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListAnyDirectDemo --out /tmp/leanListAnyDirectDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListAnyDirectMissingDemo --out /tmp/leanListAnyDirectMissingDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListAllDirectDemo --out /tmp/leanListAllDirectDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListAllDirectMissingDemo --out /tmp/leanListAllDirectMissingDemo.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListAnyDirectDemo /tmp/leanListAnyDirectDemo.wasm` returned `1`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListAnyDirectMissingDemo /tmp/leanListAnyDirectMissingDemo.wasm` returned `0`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListAllDirectDemo /tmp/leanListAllDirectDemo.wasm` returned `1`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListAllDirectMissingDemo /tmp/leanListAllDirectMissingDemo.wasm` returned `0`.
- [x] `node test/core_correctness.js` returned `checked 495 accepted, 24 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 495 accepted, 24 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Recursive list-valued helpers

Structural-recursion extraction now preserves the structural-recursion error when a recursive helper fails to lower, instead of trying the closed-fold path for helpers whose first parameter is already the recursive value.  The closed-fold path remains for top-level closed expressions, where it fits the generated `brecOn` shape with a hidden accumulator.  The earlier fallback hid the real failure for a source-defined append helper by reporting a closed-fold tail-call error.

Recursive branch selection now accepts a branch that returns an existing heap recursive value and another branch that constructs a fresh recursive value of the same type.  Flattening already knew how to turn both forms into the internal heap-pointer slot, so the branch combiner now keeps the conditional value lazy and lets result materialization allocate only the selected constructed branch.  This admits source-defined `List UInt64` helpers for length, append, reverse, and fold-right-style traversal.

The regression corpus records direct expression-position standard-library calls as rejected cases: direct `List.map`, `List.filter`, `List.length`, list append notation, `List.reverse`, and `List.foldr`.  Those forms need an expression-position structural-recursion lowering or another principled first-order extraction path.  The accepted cases exercise ordinary source-defined recursive helpers while the compiler remains generic over recursive inductive layouts.

Checks run:

- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListLengthRecDemo --out /tmp/leanListLengthRecDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListAppendRecDemo --out /tmp/leanListAppendRecDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListReverseRecDemo --out /tmp/leanListReverseRecDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListFoldrRecDemo --out /tmp/leanListFoldrRecDemo.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListLengthRecDemo /tmp/leanListLengthRecDemo.wasm` returned `3`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListAppendRecDemo /tmp/leanListAppendRecDemo.wasm` returned `15`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListReverseRecDemo /tmp/leanListReverseRecDemo.wasm` returned `3`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListFoldrRecDemo /tmp/leanListFoldrRecDemo.wasm` returned `321`.
- [x] `node test/core_correctness.js` returned `checked 499 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 499 accepted, 30 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Expression-position structural recursion

Expression-level `brecOn` terms with no hidden runtime post-arguments now lower through private synthetic helpers.  The collector scans beta-specialized reachable declarations, identifies closed structural-recursion expressions over supported recursive inductive instances, and appends deterministic synthetic functions to the module.  Extraction of the original expression compiles the scrutinee and emits a call to the private helper, while the helper body uses the existing structural-recursion extractor, including generated below projections and WASM self-calls.

This admits direct expression-position `List.map`, `List.filter`, and `List.foldr` over `List UInt64` when the callback specializes to closed first-order code.  The lowering is keyed on recursive-inductive layouts rather than `List` declarations.  `List.length`, list append notation, and `List.reverse` remain rejected because their generated forms do not match this expression-level structural-recursion shape.

Checks run:

- [x] `lake build LeanExe.Extract.Core`
- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListMapDirectDemo --out /tmp/leanListMapDirectDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListMapDirectBranchDemo --out /tmp/leanListMapDirectBranchDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListFilterDirectDemo --out /tmp/leanListFilterDirectDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListFoldrDemo --out /tmp/leanListFoldrDemo.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListMapDirectDemo /tmp/leanListMapDirectDemo.wasm` returned `2`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListMapDirectBranchDemo /tmp/leanListMapDirectBranchDemo.wasm 0` returned `10`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListMapDirectBranchDemo /tmp/leanListMapDirectBranchDemo.wasm 1` returned `2`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListFilterDirectDemo /tmp/leanListFilterDirectDemo.wasm` returned `2`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListFoldrDemo /tmp/leanListFoldrDemo.wasm` returned `321`.
- [x] `node test/core_correctness.js` returned `checked 504 accepted, 27 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 504 accepted, 27 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-12: Structural recursion with post-arguments

Expression-level structural-recursion lowering now synthesizes helpers that accept supported first-order post-arguments after the recursive scrutinee.  The discovery pass reduces transparent wrapper definitions only far enough to expose a supported recursive-inductive `brecOn`; it reduces projection and constructor adapters for typeclass methods, preserves default runtime arguments, and leaves the existing primitive extractors responsible for ordinary arithmetic, string, array, and byte-array operations.  The synthetic helper body replaces dynamic post-arguments with helper parameters, while direct-lambda post-arguments remain static when they are closed.

This admits direct `List.length`, list append notation through `++`, and `List.reverse` over `List UInt64` without adding compiler cases for those declarations.  The append branch example passes the right-hand list as a runtime carried value, which exercises the new post-argument path rather than a closed literal.  Runtime `Char` is now rejected by the type classifier, so compile-time string helpers such as `String.length` continue to use the string-specific ASCII path instead of being captured as generic `List Char` recursion.

Checks run:

- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListLengthDirectDemo --out /tmp/leanListLengthDirectDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListAppendDirectDemo --out /tmp/leanListAppendDirectDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListAppendDirectBranchDemo --out /tmp/leanListAppendDirectBranchDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.leanListReverseDirectDemo --out /tmp/leanListReverseDirectDemo.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListLengthDirectDemo /tmp/leanListLengthDirectDemo.wasm` returned `3`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListAppendDirectDemo /tmp/leanListAppendDirectDemo.wasm` returned `15`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListAppendDirectBranchDemo /tmp/leanListAppendDirectBranchDemo.wasm 0` returned `6`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListAppendDirectBranchDemo /tmp/leanListAppendDirectBranchDemo.wasm 1` returned `15`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke leanListReverseDirectDemo /tmp/leanListReverseDirectDemo.wasm` returned `3`.
- [x] `node test/core_correctness.js` returned `checked 509 accepted, 24 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 509 accepted, 24 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-13: Shared structural-recursion parsing

The extractor now parses recursive-inductive `brecOn` applications through `rawStructuralRecApplication?`, with `structuralRecApplication?` adding normalization for expression-position terms.  The shared record holds the constant, type arguments, motive, scrutinee, step, and post-arguments that the expression-level synthetic helper path, closed predicate path, closed fold path, top-level structural-recursion extractor, and top-level candidate detector decoded separately.  The regression counts stayed unchanged, which matches the intent of this refactor: one parser now supplies the existing lowering paths.

Checks run:

- [x] `lake build LeanExe.Extract.Core`
- [x] `lake build lean-wasm LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 509 accepted, 24 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 509 accepted, 24 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-13: Recursive pointers in fixed-width values

Internal fixed-width structures and nonrecursive tagged values can contain recursive-inductive fields because the existing layout machinery treats a recursive value as one heap-pointer slot at strict boundaries.  This is now covered by `ExprBox`, which stores a `U64Expr` inside a structure and exercises direct use plus `Array ExprBox` folding, and by `ExprSlot`, which stores a `U64Expr` inside a tagged payload and exercises direct matching plus `Array.find?`.  The public ABI still rejects those layouts when they appear as entry parameters or results, so the feature remains internal until recursive data has a documented host representation.

Checks run:

- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.recursiveStructFieldDemo --out /tmp/recursiveStructFieldDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.recursiveStructArrayFoldDemo --out /tmp/recursiveStructArrayFoldDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.recursiveTaggedPayloadDemo --out /tmp/recursiveTaggedPayloadDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.recursiveTaggedArrayFindDemo --out /tmp/recursiveTaggedArrayFindDemo.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke recursiveStructFieldDemo /tmp/recursiveStructFieldDemo.wasm` returned `21`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke recursiveStructArrayFoldDemo /tmp/recursiveStructArrayFoldDemo.wasm` returned `24`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke recursiveTaggedPayloadDemo /tmp/recursiveTaggedPayloadDemo.wasm` returned `17`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke recursiveTaggedArrayFindDemo /tmp/recursiveTaggedArrayFindDemo.wasm` returned `19`.
- [x] `node test/core_correctness.js` returned `checked 513 accepted, 26 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 513 accepted, 26 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-13: Internal mutual recursive inductives

Recursive-inductive layout classification now uses Lean's `InductiveVal.all` family list.  A field inside a recursive family may refer to any member of the same specialized family, so a `MutJson` constructor can store an `Array MutField`, and a `MutField` constructor can store a `MutJson`.  Each family member still lowers to the existing one-slot heap-pointer representation at strict boundaries.  At this point, public entry parameters and results still rejected recursive-family values, and mutual structural recursion and mutual recursive helper functions remained outside the accepted language.

The correctness corpus now includes a `MutJson` and `MutField` pair, direct array construction over `MutJson`, object-like arrays over `MutField`, a structure wrapper around `MutField`, a tagged wrapper around `MutJson`, and public ABI rejection cases for both family members and arrays of family members.  Sparse constructor matches still lower to generated helpers outside the current matcher path, so the accepted examples use exhaustive matches.

Checks run:

- [x] `lake build LeanExe.Extract.Core`
- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.mutualJsonArrayDemo --out /tmp/mutualJsonArrayDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.mutualJsonObjectDemo --out /tmp/mutualJsonObjectDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.mutualWrappedFieldArrayDemo --out /tmp/mutualWrappedFieldArrayDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.mutualTaggedArrayFindDemo --out /tmp/mutualTaggedArrayFindDemo.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke mutualJsonArrayDemo /tmp/mutualJsonArrayDemo.wasm` returned `4`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke mutualJsonObjectDemo /tmp/mutualJsonObjectDemo.wasm` returned `60`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke mutualWrappedFieldArrayDemo /tmp/mutualWrappedFieldArrayDemo.wasm` returned `55`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke mutualTaggedArrayFindDemo /tmp/mutualTaggedArrayFindDemo.wasm` returned `102`.
- [x] `node test/core_correctness.js` returned `checked 517 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 517 accepted, 30 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-13: Two-branch mutual structural recursion

Ordinary two-function mutual structural recursion over two members of the same recursive family now compiles through Lean's generated `WellFounded.Nat.fix` helper over `PSum`.  The extractor treats `PSum` as an internal sum layout, compiles the generated mutual helper as an internal function with tag-plus-payload parameters, and consumes the hidden well-founded binder in each member's generated constructor matcher.  Recursive calls inside those constructor arms use the same well-founded handle, including calls inside fixed-width `Array.attach` folds over family members.

The correctness corpus now includes `mutJsonDeepSize` and `mutFieldDeepSize`, which traverse `MutJson` and `MutField` through both direct fields and arrays.  The supported shape is still narrow: it covers the binary `PSum` helper that Lean generates for ordinary two-function mutual definitions.  Broader mutual groups, non-family `PSum` recursion, public recursive values, and arbitrary well-founded recursion remain outside the accepted language.

Checks run:

- [x] `lake build LeanExe.Extract.Core`
- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.mutualStructuralJsonSizeDemo --out /tmp/mutualStructuralJsonSizeDemo.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.mutualStructuralFieldSizeDemo --out /tmp/mutualStructuralFieldSizeDemo.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke mutualStructuralJsonSizeDemo /tmp/mutualStructuralJsonSizeDemo.wasm` returned `10`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke mutualStructuralFieldSizeDemo /tmp/mutualStructuralFieldSizeDemo.wasm` returned `11`.
- [x] `node test/core_correctness.js` returned `checked 519 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 519 accepted, 30 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-13: N-way mutual structural recursion

Lean lowers ordinary mutual definitions over three or more recursive-family members with a right-nested `PSum` parameter, such as `PSum A (PSum B C)`, and a single generated `WellFounded.Nat.fix` helper.  The extractor now parses that nested `PSum.casesOn` tree recursively.  Each leaf must still match one supported recursive-family member, and each member branch still goes through the existing generated-matcher checks for direct recursive fields and fixed-width `Array.attach` folds.

The correctness corpus now includes `TriA`, `TriB`, and `TriC`, a three-member recursive family whose constructors recurse through arrays.  `triAScore`, `triBScore`, and `triCScore` compile through the shared generated helper and produce independent entry demos for all three wrapper functions.  The accepted shape remains the Lean-generated structural form; arbitrary well-founded recursion, non-family `PSum` recursion, public recursive values, and mutual helper groups that do not structurally descend through recursive-family values remain outside the accepted language.

Checks run:

- [x] `lake build LeanExe.Extract.Core`
- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.mutualStructuralTriADemo --out .lake/build/mutual-tri-a.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.mutualStructuralTriBDemo --out .lake/build/mutual-tri-b.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.mutualStructuralTriCDemo --out .lake/build/mutual-tri-c.wasm`
- [x] `build/tools/wasmtime/current/wasmtime run --invoke mutualStructuralTriADemo .lake/build/mutual-tri-a.wasm` returned `21`.
- [x] `build/tools/wasmtime/current/wasmtime run --invoke mutualStructuralTriBDemo .lake/build/mutual-tri-b.wasm` returned `15`.
- [x] `build/tools/wasmtime/current/wasmtime run --invoke mutualStructuralTriCDemo .lake/build/mutual-tri-c.wasm` returned `15`.
- [x] `node test/core_correctness.js` returned `checked 522 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 522 accepted, 30 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-13: Concrete parameters for data layouts

User-defined structures and nonrecursive inductives now carry concrete runtime type arguments in the extracted `Ty` representation.  The extractor reconstructs the instantiated Lean type when substituting constructor fields, projection targets, matcher scrutinees, helper parameters, helper results, and array element layouts.  This fixes nested cases such as `ParamResult UInt64 (Box UInt64)`, where rebuilding the type as bare `Box` lost the `UInt64` argument and made constructor payload classification fail.

Lean registered structures now use `isStructure`, while ordinary one-constructor inductives stay on the user-inductive path.  This distinction matters because Lean's `isStructureLike` also returns true for nonrecursive single-constructor inductives with no indices, but only registered structures have field metadata for `getStructureFieldsFlattened`.  The bug surfaced through `CheckedPayload`, a one-constructor inductive with a proof-erased field, which must compile as a tagged value rather than as a structure.

Concrete parametric structures also exposed a dependency-collection boundary around type-class evidence.  `Inhabited Slot` became a supported structure-shaped type once parametric structures were allowed, which pulled the derived `instInhabitedSlot.default` helper into the compiled call graph for array bang indexing.  Evidence carrier types such as `Inhabited`, `BEq`, arithmetic classes, ordering classes, and `GetElem` classes are now rejected as runtime data, so primitive extractors consume their applications without compiling the instance values as ordinary helpers.

Checks run:

- [x] `lake build LeanExe.Extract.Core`
- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 537 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 537 accepted, 30 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-13: Inline specialization for polymorphic helpers

The extractor now recognizes local first-order polymorphic helper applications whose static type or proof arguments precede all runtime arguments.  At a concrete call site, it substitutes those static arguments into the helper body, derives the concrete runtime parameter and result types from the instantiated function type, and reuses the existing inline extraction path for the remaining runtime arguments.  This keeps the first slice small: there is no shared generic runtime function, no typeclass specialization, and no escaping function value.

The specialized inline path preserves the existing lazy argument behavior.  The correctness corpus includes a polymorphic helper that returns the first `Box` value while the unused second `Box` contains an out-of-bounds array read; the generated WASM returns the first value rather than evaluating the unused argument.  Other examples cover `Box α -> α`, projections from `PairBox α β`, boolean matching over `ParamResult ε α`, extracting a `Point` through a polymorphic result helper, and extracting a value from `CheckedPayload α`.

Checks run:

- [x] `lake build LeanExe.Extract.Core`
- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 543 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 543 accepted, 30 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-13: Layout-driven internal array elements

The extractor now has an explicit `ValueLayout` model for scalar, fixed-width, and pointer-shaped runtime values.  Array element widths come from that layout instead of from a hand-written list of surface types.  Internal arrays can store nested arrays as one pointer slot, products as their flattened slot sequence, and structures or tagged values whose fields include array or recursive pointer slots.

The public array ABI remains conservative.  Entry parameters and results still accept scalar, structure, and tagged fixed-width array elements only when their layouts contain no nested heap references.  The correctness corpus now includes public rejection cases for nested-array parameters, nested-array results, and arrays of structures that contain array fields.

This work exposed an older internal-call layout bug.  Non-exported helper functions now use internal parameter and result layouts, so products and other internal-only multi-slot values can cross real WASM calls without being treated as public ABI values.  The inline decision also checks strict materialization safety for multi-slot arguments, preserving lazy projection behavior when an unused field contains a trapping expression.

Checks run:

- [x] `lake build LeanExe.Extract.Core`
- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 550 accepted, 32 rejected, and 13 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.nestedArrayMapPushRead --out /tmp/nestedArrayMapPushRead.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayBoxElementRead --out /tmp/arrayBoxElementRead.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayProductElementRead --out /tmp/arrayProductElementRead.wasm`
- [x] `build/tools/wasmtime/current/wasmtime run --invoke nestedArrayMapPushRead /tmp/nestedArrayMapPushRead.wasm` returned `299`.
- [x] `build/tools/wasmtime/current/wasmtime run --invoke arrayBoxElementRead /tmp/arrayBoxElementRead.wasm` returned `223`.
- [x] `build/tools/wasmtime/current/wasmtime run --invoke arrayProductElementRead /tmp/arrayProductElementRead.wasm` returned `43`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 550 accepted, 32 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-13: Structured direct fold accumulators

Direct `Array.foldl` and `ByteArray.foldl` now use the same internal-slot accumulator model as accepted pure `Id.run` `for` loops.  The extractor reconstructs the accumulator from loop-local slots, extracts the direct-lambda body as a structured value, flattens the body result, and rebuilds the requested source-level result value from the projected fold slots.  At this checkpoint, supported accumulator shapes were scalars, supported array pointers, products, structures, nonrecursive tagged values, and recursive-inductive pointer values, provided the flattened accumulator contained no `ByteArray` field.

The correctness corpus now covers direct folds carrying a `CountSum` structure, a product, a `Status` tagged value, and an array pointer.  It covers both `Array.foldl` and `ByteArray.foldl`, and it rejected direct folds whose accumulator was a `ByteArray`.  The later `ByteArray` accumulator entry supersedes that limitation.

Checks run:

- [x] `lake build`
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 558 accepted, 34 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-13: Unified direct fold lowering

The scalar-only direct fold path has been removed.  `extractExprFrom` now handles scalar uses of `Array.foldl` and `ByteArray.foldl` by extracting the same value-level fold representation used for structured accumulators, then projecting the scalar result.  The IR and WASM emitters no longer contain the old one-slot `arrayFoldSlots` and `byteArrayFold` expression forms.

The shared accumulator predicate is now named `supportedLoopAccumulatorType`, because pure `for` loops and direct folds use the same accumulator layout.  Existing scalar fold correctness cases now exercise the multi-slot fold IR with result width one, while the structured fold cases exercise the same code path at larger widths.

Checks run:

- [x] `lake build`
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 558 accepted, 34 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayFoldSum --out .lake/build/core-correctness/arrayFoldSum.unified.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.byteArrayFoldSum --out .lake/build/core-correctness/byteArrayFoldSum.unified.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayFoldSum --out .lake/build/core-correctness/arrayFoldSum.unified.wat`
- [x] `build/tools/wasmtime/current/wasmtime --invoke arrayFoldSum .lake/build/core-correctness/arrayFoldSum.unified.wasm` returned `6`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke byteArrayFoldSum .lake/build/core-correctness/byteArrayFoldSum.unified.wasm` returned `6`.
- [x] `wc -c .lake/build/core-correctness/arrayFoldSum.unified.wat` returned `11373`.

## 2026-05-13: Slot-width array IR cleanup

The one-slot array expression forms have been removed from the IR and the WASM emitters.  Scalar arrays now use the same slot-width representation as arrays of products, structures, tagged values, recursive pointers, and nested array pointers, with scalar elements represented as width one.  Scalar reads from primitive `Array` indexing lower to `arrayGetSlot 1 0`, so extraction no longer needs a separate scalar array read constructor.

This removes the duplicate allocation, replication, update, push, pop, append, extract, map, insert, erase, swap, and reverse emitter paths.  The remaining array representation still stores the logical length in the array header and stores the element payload as `length * width` contiguous 64-bit cells.  The public ABI restrictions remain unchanged: nested heap references may appear in internal arrays but still cannot cross exported function boundaries as public array parameters or results.

Checks run:

- [x] `lake build`
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 558 accepted, 34 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.

## 2026-05-14: ByteArray loop and fold accumulators

`ByteArray` now participates in the shared internal accumulator layout for pure `Id.run` `for` loops, `Array.foldl`, and `ByteArray.foldl`.  The representation uses the existing two-slot pointer-length value, so byte-producing loops and folds require no new WASM expression form.  Products, structures, and tagged values can carry `ByteArray` fields through the same accumulator path when their other fields are supported.

The correctness corpus now covers byte-producing `ByteArray` loops, `break`, `continue`, range loops, `Array.foldl` with a `ByteArray` accumulator, `ByteArray.foldl` with a `ByteArray` accumulator, and structures that carry a `ByteArray` field as part of the accumulator.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build lean-wasm`
- [x] `node test/core_correctness.js` returned `checked 566 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 566 accepted, 30 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayFoldStructAccumulator --out .lake/build/core-correctness/arrayFoldStructAccumulator.wasmtime.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.byteArrayFoldStatusAccumulator --out .lake/build/core-correctness/byteArrayFoldStatusAccumulator.wasmtime.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke arrayFoldStructAccumulator .lake/build/core-correctness/arrayFoldStructAccumulator.wasmtime.wasm` returned `36`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke byteArrayFoldStatusAccumulator .lake/build/core-correctness/byteArrayFoldStatusAccumulator.wasmtime.wasm` returned `24`.

## 2026-05-14: Public UInt8 and UInt32 ABI

`UInt8` and `UInt32` now cross the public entry ABI as one `i64` slot each.  Public parameters normalize at function entry by masking to `2^8 - 1` or `2^32 - 1`, and public results normalize before returning to the host.  This matches the fixed-width representation already used by literals, conversions, arithmetic, arrays, and byte-oriented helper code inside the compiler subset.

The former public-scalar rejection fixtures now compile as ordinary examples.  `uint8ParamToNat` and `uint32ParamToNat` test parameter normalization from oversized host arguments, while `uint8Return` and `uint32Return` test result normalization from oversized Lean literals.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build lean-wasm`
- [x] `node test/core_correctness.js` returned `checked 570 accepted, 26 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 570 accepted, 26 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, and `checked 56 cases`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke uint8ParamToNat .lake/build/core-correctness/uint8ParamToNat.public.wasm 300` returned `44`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke uint8Return .lake/build/core-correctness/uint8Return.public.wasm` returned `44`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke uint32ParamToNat .lake/build/core-correctness/uint32ParamToNat.public.wasm 4294967297` returned `1`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke uint32Return .lake/build/core-correctness/uint32Return.public.wasm` returned `1`.

## 2026-05-14: WASI ByteArray stdout programs

`compile-wasi` adds a command-style target for pure entries that take no parameters and return `ByteArray`.  The generated module imports `wasi_snapshot_preview1.fd_write`, exports `_start`, calls the compiled Lean entry, writes the returned byte range to stdout, and traps when `fd_write` reports an error or a short write.  This keeps Lean `IO` outside the source language while giving byte-producing programs observable output under Wasmtime.

The WASI target reuses the same extracted function bodies as library mode.  Because imported functions occupy the start of the WASM function-index space, the emitter shifts internal call indices by the number of imports before encoding command modules.  The command module exports memory and `_start`; it does not expose the selected Lean entry, `alloc`, or `reset` as its program interface.

Checks run:

- [x] `lake build lean-wasm`
- [x] `node test/core_correctness.js` returned `checked 570 accepted, 26 rejected, and 13 trapped cases`.
- [x] `node test/wasi_program.js` returned `checked 4 WASI program cases and 2 rejections`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 570 accepted, 26 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, `checked 4 WASI program cases and 2 rejections`, and `checked 56 cases`.
- [x] `.lake/build/bin/lean-wasm compile-wasi --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.byteArrayStringConstReturn --out .lake/build/core-correctness/byteArrayStringConstReturn.wasi.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wasi --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.byteArrayAppendReturn --out .lake/build/core-correctness/byteArrayAppendReturn.wasi.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wasi --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.byteArrayPushSize --out .lake/build/core-correctness/bad-non-bytearray.wasm` rejected with `program entry must return ByteArray`.
- [x] `build/tools/wasmtime/current/wasmtime run .lake/build/core-correctness/byteArrayStringConstReturn.wasi.wasm` returned `XYZ`.
- [x] `build/tools/wasmtime/current/wasmtime run .lake/build/core-correctness/byteArrayAppendReturn.wasi.wasm` returned `ABC`.

## 2026-05-14: WASI bounded stdin programs

`compile-wasi-stdin` adds a bounded stdin-to-stdout command target for pure entries of type `ByteArray -> ByteArray`.  The generated `_start` imports `wasi_snapshot_preview1.fd_read` and `fd_write`, reads stdin into the arena until EOF, traps if input exceeds the explicit `--max-input-bytes` limit, calls the compiled Lean entry with the input pointer and length, and writes the returned byte range to stdout.  This keeps input effects in the generated adapter rather than in Lean source code.

The adapter reserves `max-input-bytes + 1` bytes so it can distinguish EOF exactly at the limit from input that exceeds the limit.  The maximum configured limit must fit in the initial 16-page memory after the arena start at byte offset `4096`.  Imported functions shift the WASM function-index space by two for stdin modules, so the emitter reuses the existing call-index shifter with offset `2`.

Checks run:

- [x] `lake build lean-wasm`
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin --max-input-bytes 8 --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.byteArrayIdentityReturn --out .lake/build/wasi-programs/byteArrayIdentityReturn.stdin.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin --max-input-bytes 8 --module LeanExe.Examples.ByteArrayPrograms --entry LeanExe.Examples.ByteArrayPrograms.appendBang --out .lake/build/wasi-programs/appendBang.stdin.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin --max-input-bytes 8 --module LeanExe.Examples.ByteArrayPrograms --entry LeanExe.Examples.ByteArrayPrograms.tailSlice --out .lake/build/wasi-programs/tailSlice.stdin.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin --max-input-bytes 8 --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.byteArrayStringConstReturn --out .lake/build/wasi-programs/bad-stdin-shape.wasm` rejected with `program stdin entry must have type ByteArray -> ByteArray`.
- [x] `compile-wasi-stdin` rejects `--max-input-bytes 1048576` with `max input bytes exceeds WASM memory capacity`.
- [x] `printf AB | build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/byteArrayIdentityReturn.stdin.wasm` returned `AB`.
- [x] `printf AB | build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/appendBang.stdin.wasm` returned `AB!`.
- [x] `printf ABC | build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/tailSlice.stdin.wasm` returned `BC`.
- [x] `printf ABCDEFGHI | build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/byteArrayIdentityReturn.stdin.wasm` trapped on input limit.
- [x] `node test/wasi_program.js` returned `checked 7 WASI program cases, 1 stdin trap, and 4 rejections`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 570 accepted, 26 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, `checked 7 WASI program cases, 1 stdin trap, and 4 rejections`, and `checked 56 cases`.

## 2026-05-14: WASI error-result programs

`compile-wasi-stdin-except` adds a command target for pure entries of type `ByteArray -> Except ByteArray ByteArray`.  The generated `_start` uses the same bounded `fd_read` input path as `compile-wasi-stdin`.  It decodes the public `Except` result as tag, error pointer, error length, ok pointer, and ok length.  Tag `1` writes the ok payload to stdout and returns normally.  Tag `0` writes the error payload to stderr and calls `wasi_snapshot_preview1.proc_exit` with status `1`.

The WASI emitter now builds command-module type sections from an explicit list of import function types.  `fd_read` and `fd_write` share the `[i32, i32, i32, i32] -> i32` type, while `proc_exit` uses `[i32] -> []`.  Module function type indices start after those import types, and module function indices start after the imported functions, so the existing call-index shifter still has one concrete offset per command adapter.

Checks run:

- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/wasi_program.js` returned `checked 9 WASI program cases, 1 stdin trap, and 5 rejections`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 570 accepted, 26 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, `checked 9 WASI program cases, 1 stdin trap, and 5 rejections`, and `checked 56 cases`.

## 2026-05-14: WASI argv programs

`Array ByteArray` is now a supported internal array shape.  Each element stores two slots, the byte pointer and byte length, using the same internal `ByteArray` representation used for locals and helper calls.  Public `Array ByteArray` parameters and results remain rejected because the library-mode host ABI still excludes arrays with heap-reference elements.

`compile-wasi-argv-except` adds a command target for pure entries of type `Array ByteArray -> Except ByteArray ByteArray`.  The generated `_start` imports `args_sizes_get`, `args_get`, `fd_write`, and `proc_exit`.  It allocates a fixed arena region from the configured `--max-args` and `--max-argv-bytes`, reads WASI argv into that region, skips `argv[0]`, builds an internal array of user-argument byte slices, calls the Lean entry, writes `Except.ok` bytes to stdout, and writes `Except.error` bytes to stderr before `proc_exit 1`.

Checks run:

- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/core_correctness.js` returned `checked 574 accepted, 28 rejected, and 13 trapped cases`.
- [x] `node test/wasi_program.js` returned `checked 11 WASI program cases, 2 traps, and 7 rejections`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 574 accepted, 28 rejected, and 13 trapped cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 46 json program cases`, `checked 11 WASI program cases, 2 traps, and 7 rejections`, and `checked 56 cases`.

## 2026-05-14: JSON tree pipeline

`LeanExe.Examples.JsonTreeCommand` adds a two-command JSON pipeline.  `makeTree` reads a JSON array through `compile-wasi-stdin-except`, builds a source-level recursive binary-search tree, and writes the tree as nested JSON.  `searchTree` reads that tree JSON through stdin, reads the search key from argv through `compile-wasi-stdin-argv-except`, and writes a JSON boolean result.

The example exposed three compiler issues.  Structural recursion with captured non-scrutinee parameters now passes those parameters through direct recursive-field calls, which lets ordinary definitions such as `insert tree value` compile without source reshaping.  Fuel recursion now lowers tail-position control flow under nested `if`, dependent `if`, `Bool` matches, `Option` matches, and supported nonrecursive inductive matches, which lets parser-style loops return early or recur from natural source branches.

The same example also exposed duplicated evaluation of byte-array operand expressions.  `ByteArray.push`, `ByteArray.append`, and byte-array append notation now bind operand pointer-length pairs before constructing the result, so a recursive byte-producing helper used as an operand runs once.  The stdin-plus-argv WASI adapter now aligns the arena before building the argv pointer table, matching the alignment expected by WASI `args_get`.

Checks run:

- [x] `lake build lean-wasm`
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin-except --max-input-bytes 4096 --module LeanExe.Examples.JsonTreeCommand --entry LeanExe.Examples.JsonTreeCommand.makeTree --out .lake/build/make-tree.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin-argv-except --max-input-bytes 8192 --max-args 8 --max-argv-bytes 256 --module LeanExe.Examples.JsonTreeCommand --entry LeanExe.Examples.JsonTreeCommand.searchTree --out .lake/build/search-tree.wasm`
- [x] `printf '%s' '[1,6,4,100,33,5,5,20]' | build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime .lake/build/make-tree.wasm | build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime .lake/build/search-tree.wasm 4` returned `{"found":true}`.
- [x] `printf '%s' '[1,6,4,100,33,5,5,20]' | build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime .lake/build/make-tree.wasm | build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux/wasmtime .lake/build/search-tree.wasm 7` returned `{"found":false}`.

## 2026-05-14: Reference-counted heap runtime

Library-mode modules now allocate heap-backed payloads behind a small reference-counted header in WASM linear memory.  The payload pointer remains the public pointer, so array length headers and byte-array contents keep their existing ABI positions.  The runtime stores reference count, payload capacity, object kind, and two descriptor fields immediately before the payload, and it reuses released blocks through a first-fit free list.

The library ABI now exports `retain`, `release`, and `free` in addition to `alloc` and `reset`.  `alloc` creates a raw byte object with count `1`, `retain` increments a nonzero object's count and returns the same pointer, and `release` decrements the count and returns the block to the free list at zero.  `free` is an alias for `release` for hosts that expect that name.

This is the runtime foundation for compiler-emitted reclamation, not full ownership analysis.  Generated code now gives byte arrays, arrays, and recursive-inductive heap objects RC headers, and hosts can release returned objects.  The compiler still needs a type-directed ownership pass before it can release dead internal temporaries inside one call without risking use-after-free.

Checks run:

- [x] `lake build`
- [x] `node test/refcount.js` returned `checked 3 refcount cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 574 accepted, 28 rejected, and 13 trapped cases`, `checked 3 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 19 WASI program cases, 2 traps, and 7 rejections`, and `checked 56 cases`.

## 2026-05-14: Conservative compiler-emitted releases

The IR now has a `release` statement, and the binary emitter passes the runtime release-function index into user-function emission.  Library modules call the exported release runtime.  WASI command modules define the same release runtime after `_start`, so compiled user functions have a valid target when the extractor emits a release in command mode.

The extractor emits releases for a narrow ownership case: a local expression or local binding must assign a value whose final expression returns a fresh heap allocation, and the surrounding function result type must contain no heap pointer.  This keeps returned heap values conservative while reclaiming scalar-result temporaries such as `let a := Array.replicate 1 (5 : UInt64); ... a[0]! ...`.  The pass follows expression lets to find the allocated value and handles one-slot heap allocations inside `LocalLet.slots`.  It does not release call results, loop-carried values, heap-pointer result aliases, or values whose last use occurs before the final result assignment.

`test/refcount.js` now checks this compiler path by compiling `LeanExe.Examples.ByteArrayPrograms.firstBytePlusArray`, calling it with a byte-array input, and verifying that the next 16-byte allocation reuses the internal array block.  The test derives the expected block location from allocator behavior after `reset()`, rather than from a hard-coded header size.

Checks run:

- [x] `lake build`
- [x] `node test/refcount.js` returned `checked 4 refcount cases`.
- [x] `node test/run_all.js` returned `checked 92 report classification cases`, `checked 574 accepted, 28 rejected, and 13 trapped cases`, `checked 4 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 19 WASI program cases, 2 traps, and 7 rejections`, and `checked 56 cases`.

## 2026-05-15: Array child release for recursive values

Array allocation now records a child mask for recursive-inductive pointer slots in the fixed-width element layout.  The mask follows products, structures, and nonrecursive tagged values, but it does not mark `ByteArray` fields or nested array fields.  Those pointer shapes can name borrowed input storage, byte-array slices, or WASI adapter arrays, so treating them as owned RC roots would make correct programs trap.

Array-producing operations now retain recursive child pointers when they copy existing elements into a new array.  Inserted values also carry an owned-child mask, so a freshly constructed recursive value can be transferred into the new array without an extra retain while a borrowed recursive value is retained before sharing.  `Array.replicate` treats the first replicated owned child as the transferred reference and retains the remaining references.

`LeanExe.Runtime.release` now accepts compiler-owned array roots as well as monomorphic recursive-inductive roots.  The ownership precondition is unchanged: source code must release only a value that will not be used again, and the compiler does not prove that condition.  Releasing a host-owned public array pointer or a WASI adapter array violates the runtime representation and may trap.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.u64ListArrayRuntimeReleaseFrees --out .lake/build/u64ListArrayRuntimeReleaseFrees.wasm`
- [x] `build/tools/wasmtime/current/wasmtime run --invoke u64ListArrayRuntimeReleaseFrees .lake/build/u64ListArrayRuntimeReleaseFrees.wasm` returned `103`.
- [x] `node test/core_correctness.js` returned `checked 611 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 611 accepted, 29 rejected, and 13 trapped cases`, `checked 5 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 38 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-15: ByteArray owner slots in stored values

`ByteArray` now has separate public and internal layouts.  Public entry parameters and results still use pointer and length slots, which keeps the host ABI stable.  Internal values use owner, pointer, and length slots, where owner `0` marks borrowed storage and a nonzero owner names the reference-counted allocation root.

Byte-array constructors that allocate new buffers set owner equal to the allocated pointer.  `ByteArray.extract` preserves the source owner while changing the visible pointer and length, so a slice stored in an array, structure, or tagged value can keep the root allocation alive.  The release child mask now marks `ByteArray` owner slots in recursive values and fixed-width array elements, while nested array fields remain outside recursive release until their representation carries equivalent owner metadata.

The extractor also tracks owned aliases through local `let` bindings when it decides whether a child slot transfers ownership into a newly allocated array or heap object.  Explicit `LeanExe.Runtime.release` calls suppress compiler-emitted cleanup for the released slot, which prevents a user-declared ownership boundary from being followed by an automatic second release.  The WASI argv adapters now build internal `Array ByteArray` values with three-slot elements and consume the seven-slot internal result for `Except ByteArray ByteArray` entries.

Checks run:

- [x] `lake build LeanExe.Extract.Core LeanExe.Examples.Correctness lean-wasm`
- [x] `node test/core_correctness.js` returned `checked 612 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/refcount.js` returned `checked 6 refcount cases`.
- [x] `lake build LeanExe.Wasm.Binary LeanExe.Examples.ByteArrayPrograms lean-wasm`
- [x] `node test/wasi_program.js` returned `checked 22 WASI program cases, 2 traps, and 7 rejections`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 612 accepted, 29 rejected, and 13 trapped cases`, `checked 6 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 38 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-15: Owned helper-call result cleanup

The release pass now reclaims owner slots from helper-call results in scalar-result functions when the callee has no heap-bearing parameters.  This covers helper results such as an owned `Array UInt64`, an owned `ByteArray`, or a fixed-width structure containing both, while avoiding helpers such as `AsciiString.ofTrustedByteArray` that return a borrowed owner from a caller-owned byte array.  The rule is conservative because the compiler still lacks a helper-result ownership summary.

This work also fixed internal result materialization for heap fields inside structures and tagged values.  A structure result that contains `Array` or `ByteArray` fields now evaluates each inline heap field once, then copies owner and pointer slots from that one local value.  Without that rule, one field expression could allocate separately for the owner slot and visible pointer slot, which made later release either leak or reclaim the wrong allocation.

The GC tree rewrite WASI test now allows nonzero frees before the explicit rewrite loop.  Compiler-emitted cleanup can release temporary helper-call results before that metric is sampled, so the test checks the invariant that allocations exceed initial frees and that later explicit releases advance the counters.

Checks run:

- [x] `lake build lean-wasm`
- [x] `node test/refcount.js` returned `checked 14 refcount cases`.
- [x] `node test/core_correctness.js` returned `checked 617 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node test/wasi_program.js` returned `checked 22 WASI program cases, 2 traps, and 7 rejections`.
- [x] `node test/asciistring.js` returned `checked 23 asciistring cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 617 accepted, 29 rejected, and 13 trapped cases`, `checked 14 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 38 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-15: Extractor module split

`LeanExe.Extract.Core` now imports two new modules that keep public declarations in the same namespace.  `Types.lean` contains the core aliases, signatures, extracted values, binding context, type recognition, layout rules, supported type predicates, and reachability helpers.  `Values.lean` contains binding lookup, primitive recognition, liveness pruning, value flattening, ownership and release analysis, and result materialization.

This first split preserves declaration names and behavior.  It reduces `Core.lean` from 12,696 to 9,168 lines and creates a boundary before heap loading and expression extraction.  Later splits can move heap loading, array and byte-array lowering, matcher decoding, demand analysis, and recursion lowering without mixing redesign into the mechanical refactor.

Checks run:

- [x] `lake build lean-wasm`
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 617 accepted, 29 rejected, and 13 trapped cases`, `checked 14 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 38 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Monadic loops

The extractor now carries the selected `ForIn.forIn` monad through the existing checked-loop lowering.  `Id` loops use the previous `ForInStep` body extraction, while `Option` and `Except ε` loops carry the accumulator as `Option α` or `Except ε α`, unwrap the successful payload for the body, and stop after `none`, `Except.error`, or `ForInStep.done`.  The implementation follows Lean's checked term for `for`, `while`, `break`, and `continue`, so those source forms share one lowering path.

The correctness corpus covers `Except` loops over fixed-width arrays, `Option` loops over `ByteArray`, `Except` range loops with `break`, `Option` array loops with `continue`, and an `Option` source `while` loop through `Lean.Loop`.  The standard comparison harness now checks representative monadic-loop entries against the official Lean toolchain.  `spec.md`, `manual.md`, `README.md`, and `plan.md` describe loops in `Id`, `Option`, and `Except` as the accepted surface when the collection and accumulator layouts are supported.

Checks run:

- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 687 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 89 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 687 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 89 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-20: Heap-valued monadic loop accumulators

The monadic loop tests now cover `Option` and `Except` loops whose accumulator is a `ByteArray` or a structure containing a `ByteArray`.  These cases exercise the ownership path where each iteration constructs a fresh heap value and replaces the previous accumulator.  The extractor now reduces constant IR conditions through simple local lets, tracks constants through local-let ownership analysis, and recognizes constant-source monadic binds before choosing the generic bind lowering.  Heap-valued bind sources use the materialized path so the continuation receives stable local slots instead of re-demanding separate fields of a heap result.

The release-counter examples originally showed the remaining ownership issue after this slice.  `Option ByteArray` reported the intended two loop-replacement releases for a three-byte output, while `Except UInt64 ByteArray` and `Option ByteOutputState` exposed duplicate demand in their stat examples.  The later atomic multi-slot fold pruning change fixes that demand issue by preserving one materialized fold assignment when only part of a tagged or structured result is live.

Checks run:

- [x] `lake build LeanExe.Extract.Core`
- [x] `lake build lean-wasm LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 695 accepted, 30 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 94 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 695 accepted, 30 rejected, and 13 trapped cases`, `checked 25 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 94 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-18: Captured structural recursion

Expression-position structural recursion now records loose de Bruijn variables in the generated motive, step, and direct-lambda post-arguments.  When those loose variables refer to supported first-order locals, the extractor synthesizes a private helper whose first parameter is the recursive scrutinee and whose later parameters carry the captured values.  The synthetic helper rebases the captured references into that new parameter context, so recursive calls produced from Lean's generated below value reuse the same captured values.

The correctness examples now exercise recursive-data programs that return structures, map and transform binary trees, return `Option U64Binary` and `Except UInt64 U64Binary`, and use a tree predicate with a non-recursive `needle` parameter before the recursive tree argument.  The last case exposed the original failure mode: the extractor had generated a synthetic helper whose step still referenced the outer `needle` binder, producing an unbound de Bruijn variable during extraction.  The fix keeps the source program shape ordinary Lean code rather than rewriting examples to put the recursive argument first.

Checks run:

- [x] `lake build LeanExe.Extract.Core`
- [x] `lake build lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 627 accepted, 29 rejected, and 13 trapped cases`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 47 standard Lean comparison cases`.
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 627 accepted, 29 rejected, and 13 trapped cases`, `checked 14 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 47 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-15: Storage lowering module split

`LeanExe.Extract.Storage` now contains heap loads, field flattening from runtime field kinds, array-element flattening, strict-slot materialization, array load/find/local reconstruction, internal-slot reconstruction, public and internal parameter bindings, function parameter targets, and constructor-field binding helpers.  `Core.lean` imports that module and now begins with generic matcher and control-flow helpers.

This split preserves declaration names and behavior.  It reduces `Core.lean` from 9,168 to 8,496 lines.  The next clean boundary is matcher decoding because `Core.lean` now opens with helpers for `Option`, `Except`, `ForIn`, generated matchers, structures, and variants.

Checks run:

- [x] `lake build lean-wasm`
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 617 accepted, 29 rejected, and 13 trapped cases`, `checked 14 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 38 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-15: Pattern recognition module split

`LeanExe.Extract.Patterns` now contains constructor type helpers, monad and `ForIn` recognition, array-attach generated matcher helpers, list literal recognition, generated matcher scrutinee discovery, and matcher decoding for `Option`, `Except`, `Bool`, `Nat`, products, `PSum`, structures, and variants.  `Core.lean` imports that module and now begins with demand analysis.

This split preserves declaration names and behavior.  It reduces `Core.lean` from 8,496 to 7,694 lines.  Demand analysis is now the next clean module boundary, followed by structural and well-founded recursion lowering.

Checks run:

- [x] `lake build lean-wasm`
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 617 accepted, 29 rejected, and 13 trapped cases`, `checked 14 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 38 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-18: Demand analysis module split

`LeanExe.Extract.Demand` now contains the demand-set helpers, `Demand`, `DemandSummary`, structural equality demand helpers, expression and condition demand analysis, `demandSummary`, `mayTrapExpr`, and strict-call materialization checks.  `Core.lean` imports that module and now begins with structural-recursion recognition and lowering.

This split preserves declaration names and behavior.  It reduces `Core.lean` from 7,694 to 6,627 lines.  Structural recursion is now the next clean module boundary; after that, well-founded and Nat recursion lowering can move into a second recursion-focused module or a sibling module.

Checks run:

- [x] `lake build lean-wasm`
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 617 accepted, 29 rejected, and 13 trapped cases`, `checked 14 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 38 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-18: Structural recursion module split

`LeanExe.Extract.StructuralRec` now contains `brecOn` recognition, structural normalization, expression-shaped structural recursion synthesis, structural matcher parsing, recursive-field below bindings, structural arm binder consumption, closed structural predicate shape recognition, and Nat recursor projection recognition.  `Core.lean` imports that module and now begins with the extraction mutual block.

This split preserves declaration names and behavior.  It reduces `Core.lean` from 6,627 to 6,015 lines.  The next boundary is the extraction mutual block itself; it should be split with more care because it contains value extraction, scalar extraction, condition extraction, and primitive lowering in one mutual recursion.

Checks run:

- [x] `lake build lean-wasm`
- [x] `node test/run_all.js` returned `checked 94 report classification cases`, `checked 617 accepted, 29 rejected, and 13 trapped cases`, `checked 14 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 22 WASI program cases, 2 traps, and 7 rejections`, `checked 38 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-06-19: Talos association-list example

`LeanExe.Examples.TalosAssocList` defines an ordinary Lean association-list lookup over `List (UInt64 × UInt64)`.  The exported `lookupDemo` function takes a `UInt64` key, searches a fixed source-level list of pairs, returns the first matching value, and returns `0` for a miss.  This keeps recursive data internal while exercising product element layout, source-level product destructuring in a list constructor arm, and direct structural recursion through the generated list matcher.

The compiler change belongs in structural-recursion arm binding, not in `List` or association-list recognition.  Lean elaborates a source pattern such as `(k, v) :: rest` into separate lambdas for the pair fields before the recursive tail, while the constructor field layout remains one product value.  `consumeStructuralArmBinders` now expands an expected product runtime binder into projected field binders when the arm lambda destructures the product, preserving the previous single-binder path when the source keeps the product intact.

The Talos artifact decodes the generated WASM for `lookupDemo` and proves the exported function for every `UInt64` key.  The proof uses a concrete generated-constructor lemma for `func1`, expressed as a Boolean summary of Talos `run 5000` so it avoids equality over the whole `Store`; the summary exposes the root pointer, the list-cell memory layout, and the memory bound needed by loads.  The recursive search proof is symbolic over the key: each suffix theorem follows the generated `func0` body, splits on the stored key comparison, reads the hit value, or calls the theorem for the tail pointer.  The selected Wasmtime executions remain useful examples, but the Talos theorem no longer depends on enumerating those keys.

Checks run:

- [x] `lake build LeanExe.Examples.TalosAssocList lean-wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.TalosAssocList --entry LeanExe.Examples.TalosAssocList.lookupDemo --out build/talos-assoc-list.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke lookupDemo build/talos-assoc-list.wasm 7` returned `70`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke lookupDemo build/talos-assoc-list.wasm 2` returned `20`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke lookupDemo build/talos-assoc-list.wasm 9` returned `90`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke lookupDemo build/talos-assoc-list.wasm 5` returned `0`.
- [x] `lake build Project.AssocList.Spec` proved the all-key Talos theorem for the decoded generated WAT.
- [x] `tools/check-talos-assoc-list.sh`
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry leanPairListLookupDemo --result-slots '#[__leanexeValue]' --arg 7`
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry leanPairListLookupDemo --result-slots '#[__leanexeValue]' --arg 2`
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry leanPairListLookupDemo --result-slots '#[__leanexeValue]' --arg 5`

## 2026-06-19: WASI test compile cache

`test/wasi_program.js` now caches successful WASI compiles within one test-process run.  The cache key includes the compile mode, module name, entry name, and mode-specific limits, so input variants for one command reuse the same generated module while different modules that share an entry name such as `transform` get distinct output files.  Rejection tests still compile directly because those cases check diagnostics rather than a reusable executable artifact.

The output path now uses the same key fields instead of the entry name alone.  This removes accidental overwrites between modules such as `JsonGcd.transform`, `JsonTypedDecode.transform`, `JsonObjectArrayDecode.transform`, and `JsonGcTreeRewrite.transform`.  The final summary reports the number of successful compiles, which makes cache behavior visible without adding per-case output.

Checks run:

- [x] `node --check test/wasi_program.js`
- [x] `node test/wasi_program.js` returned `checked 35 WASI program cases, 2 traps, 7 rejections, and 19 compiles` in `217.208` seconds.

## 2026-06-19: Plain Lean association-list proof

`LeanExe.Examples.TalosAssocList` now includes `lookupDemoExpected`, `LookupSpec`, and two observation relations.  The ordinary Lean theorem `lookupDemo_correct` proves `LookupSpec leanRunsTo`; the Talos theorem now proves the same shared `LookupSpec` instantiated with `wasmRunsTo`, where `wasmRunsTo` is the generated-WASM termination-and-stack observation.  The equality theorem `lookupDemo_eq_expected` remains as the source-level helper behind the plain Lean observation.

The Talos proof project now imports `LeanExe.Examples.TalosAssocList` through a local path dependency on the root `leanexe` package.  This keeps the expected-value function and the quantified spec in one Lean module, while leaving the WASM-specific observation relation inside the Talos proof file.

Checks run:

- [x] `lake build LeanExe.Examples.TalosAssocList`
- [x] `lake build Project.AssocList.Spec`

## 2026-06-19: Simple order-book example

`LeanExe.Examples.OrderBook` defines a small single-asset central limit order book example.  The book contains one best bid and one best ask, and `matchBook` accepts both the book and incoming order as `UInt64` inputs: bid quantity, bid price, ask quantity, ask price, side flag, order quantity, and order limit price.  Side flag `0` means buy, while every other flag means sell.

The match rule emits at most one `Option Trade`.  A buy crosses when its limit price is at least the best ask price, and the trade prints at the best ask price.  A sell crosses when its limit price is at most the best bid price, and the trade prints at the best bid price.  Trade quantity is the smaller of the incoming quantity and the relevant resting quantity, and this first example does not update the book.

The standard-comparison helper writes generated files under a path derived from module and entry.  It must run sequentially for multiple inputs to the same entry, or concurrent runs can overwrite each other.  The result observation for `Option Trade` uses three scalar projections: option tag, trade quantity, and trade price.

Checks run:

- [x] `lake build LeanExe.Examples.OrderBook lean-wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.OrderBook --entry LeanExe.Examples.OrderBook.matchBook --out build/order-book.wasm`
- [x] `build/tools/wasmtime/current/wasmtime --invoke matchBook build/order-book.wasm 5 99 7 101 0 3 101` returned option tag `1`, quantity `3`, and price `101`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke matchBook build/order-book.wasm 12 200 4 250 0 9 250` returned option tag `1`, quantity `4`, and price `250`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke matchBook build/order-book.wasm 12 200 4 250 1 9 199` returned option tag `1`, quantity `9`, and price `200`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke matchBook build/order-book.wasm 12 200 4 250 1 9 201` returned option tag `0`, quantity `0`, and price `0`.

## 2026-06-19: Order-book Talos proof

The Talos proof project includes an `order_book` slice generated from the LeanExe WASM for `LeanExe.Examples.OrderBook.matchBook`.  `proofs/talos/lean/Project/OrderBook/Program.lean` is emitted from `proofs/talos/rust/build/order_book/program.wat`, and `Project.OrderBook.Spec` proves a quantified theorem about the exported `matchBook` function.  The theorem covers all seven scalar inputs: bid quantity, bid price, ask quantity, ask price, side flag, order quantity, and order limit price.

The theorem `matchBook_correct` states that the decoded WASM export terminates for every supplied one-level book and incoming order, returning exactly the expected option tag, trade quantity, and trade price.  Talos represents the WASM value stack with the top at the head of the list, so the proof names `tradeStackResult tag quantity price` as `[price, quantity, tag]`.  This is the reverse of Wasmtime's printed multi-result order, but it is the direct representation consumed by Talos's `TerminatesWith` predicate.

The proof follows the generated export `func1` and uses a separate lemma for the generated `minQty` helper `func0`.  It splits on the side flag and crossing predicate, proving the buy-crossing, buy-non-crossing, sell-crossing, and sell-non-crossing paths.  The proof artifact for this generalized scalar entry is `1207` bytes of WASM.

Checks run:

- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.OrderBook --entry LeanExe.Examples.OrderBook.matchBook --out proofs/talos/rust/build/order_book/program.wasm`
- [x] `$HOME/.cargo/bin/wasm-tools print proofs/talos/rust/build/order_book/program.wasm -o proofs/talos/rust/build/order_book/program.wat`
- [x] `proofs/talos/lean/.lake/packages/CodeLib/verifier/.lake/build/bin/verifier emit --force-emit order_book`
- [x] `lake build Project.OrderBook.Spec`
- [x] `tools/check-talos-order-book.sh`
- [x] `lake build Project`

## 2026-07-03: Talos documentation and check scripts

The top-level README now has a `Verification With Talos` section that explains the artifact proof path: LeanExe emits WASM, `wasm-tools print` renders WAT, Talos decodes the generated WAT into Lean, and the handwritten proof establishes a property of that decoded module.  The section links to the proof workspace, the Lean sources, the proof specs, and the per-case check scripts for GCD, association-list lookup, and order-book matching.  It also points users to `tools/check-talos.sh` as the combined artifact check.

`proofs/talos/README.md` now describes the proof workspace layout, the pinned Talos revision, the generated `Program.lean` files, the handwritten `Spec.lean` files, the checked-in WASM/WAT proof inputs, the current theorem scopes, the proof boundary, and the command path for regenerating `Program.lean` from an updated WAT artifact.  `spec.md` and `plan.md` now cross-reference the Talos artifact proofs while preserving the distinction between selected artifact proofs and the broader compiler-correctness theorem.  The GCD and association-list check scripts now use the same `wasm-tools print -o` form as the order-book script, and GCD now builds `Project.Gcd.Spec` instead of the whole proof project.  The combined `tools/check-talos.sh` script runs all three per-case checks and then builds the aggregate `Project` import.

Checks run:

- [x] `tools/check-talos.sh`
- [x] `git diff --check`
- [x] `bash -n tools/check-talos.sh tools/check-talos-gcd.sh tools/check-talos-assoc-list.sh tools/check-talos-order-book.sh`

## 2026-07-05: Repository summary and development agenda

`summary.md` describes the repository as it stands: the extraction pipeline, the accepted subset, the reference-counted arena memory model, the ABI and WASI adapters, the differential test suite, and the three Talos artifact proofs.  `agenda.md` sequences the next work: harden the Talos workflow, add the IR interpreter as a third differential semantics, measure heap leaks, then state and prove a lowering theorem for the scalar IR fragment, with the runtime `String` slice and backend module split behind those.  The agenda marks one design decision for discussion before the theorem work starts: whether the fragment theorem should speak about the WAT-decoded Talos module or a model built directly from the compiler's module value.

## 2026-07-06: Talos check script update mode

The three per-case check scripts are now thin wrappers over `tools/check-talos-case.sh`, which takes the case name, source module, entry, and proof spec target as flags.  The new `--update` flag replaces the checked-in proof inputs under `proofs/talos/rust/build` with fresh compiler output, regenerates the matching `Program.lean` through the Talos verifier emitter at `lean/.lake/packages/CodeLib/verifier/.lake/build/bin/verifier`, and rebuilds the proof.  Default mode keeps the byte-for-byte comparison.  `tools/check-talos.sh` forwards its arguments to all three cases.

Checks run:

- [x] `tools/check-talos-gcd.sh`
- [x] `tools/check-talos-gcd.sh --update` left a clean tree on an unchanged compiler
- [x] `tools/check-talos-assoc-list.sh`
- [x] `tools/check-talos-order-book.sh`

## 2026-07-06: IR interpreter differential column

The new `eval-ir` command compiles an entry to the core IR and evaluates it with the reference interpreter in `LeanExe/IR/Core.lean`, printing one unsigned decimal per result slot.  The interpreter is faithful only on the scalar fragment: heap constructs evaluate to `0` and `trap` evaluates to `0`.  `LeanExe/Extract/Eval.lean` therefore checks both the entry signature and the whole compiled module; any heap construct anywhere in the module exits with status `3`, and `tools/compare-standard.js` skips the IR column for that case.  The first self-test run caught exactly this: `idRunNestedArrayForSum` has a scalar signature but folds an internal array, and the signature-only check let the interpreter return `0` where WASM returned `10`.  The module scan replaced the signature-only check.

The interpreter `Store` is now a structure over `Array UInt64` with a `CoeFun` view, replacing the closure-chain function store.  The old representation added one closure per `set`, so loop evaluation was quadratic with large constants: `Collatz.steps 27` (fuel 10000) did not finish in fifteen minutes and now evaluates in under 0.2 seconds.  Extensional behavior is unchanged (`Store.empty` is all zeros, `set` shadows one index).

Pure-mode standard comparisons now run three semantics on the same inputs: standard Lean, the IR interpreter, and Wasmtime.  A mismatch localizes to extraction (standard versus IR) or emission (IR versus WASM).

Checks run:

- [x] `lean-wasm eval-ir --module LeanExe.Examples.Collatz --entry LeanExe.Examples.Collatz.steps 27` returned `111`
- [x] `lean-wasm eval-ir` on `byteArrayReturnABC` and `idRunNestedArrayForSum` exited `3` with fragment diagnostics
- [x] `node tools/compare-standard.js --self-test` returned `checked 301 standard Lean comparison cases` and `checked 58 IR interpreter comparison cases`

## 2026-07-06: Host leak accounting

Library-mode modules now export the runtime counter globals `allocCount`, `retainCount`, `releaseCount`, and `freeCount` as mutable `i64` globals, extending the reserved export-name list.  The Wasmtime host runner has a `call-stats` command that invokes an export like `call` and then prints the four counters, and `test/wasmtime_host.js` exposes `callStats`.  `test/refcount.js` asserts exact counter quadruples for seven heap-using scalar-result entries and reports the leak balance.

Five entries run leak-free (allocations equal frees): `ownedArrayCallTempScalar`, `ownedByteArrayCallTempScalar`, `ownedBoxCallTempScalar`, `sharedRecursiveChildReleaseStats`, and `byteArrayResultDropsOwnedTempStats`.  Two retain blocks at exit.  `ownedRecursiveNodeParamCallTempScalar` allocates 3 and frees 0, which is the documented conservative policy for recursive temporaries.  `arrayFoldByteArrayAccumulatorReleaseStats` allocates 11 and frees 2, so nine blocks survive a fold that the accumulator-replacement rule was thought to cover; the unreleased blocks are candidates for the next release-rule extension and should be diagnosed before new rules are written.

The export change alters every generated library module, so the three Talos proof inputs were regenerated with `tools/check-talos.sh --update`.  The WASM and WAT inputs changed, each generated `Program.lean` came back byte-identical, and all three proofs rebuilt without repair: the Talos verifier emitter's model does not reflect the export section, so the weakest-precondition proofs are untouched by added exports.

Checks run:

- [x] `node test/refcount.js` returned `checked 7 leak accounting cases, 5 leak-free, 2 retaining blocks` and `checked 38 refcount cases`
- [x] `tools/check-talos.sh --update` regenerated all three proof inputs and rebuilt all proofs

## 2026-07-06: Fragment-theorem model question

The agenda's Priority 1 needs one design decision before the theorem statement can be written.  The theorem quantifies over IR programs in the scalar fragment and asserts that the emitted WASM module, read in the Talos model, computes what `Expr.eval` computes.  The question is how the Talos-model module value is obtained.

Option A keeps the current artifact path: the emitter produces bytes, `wasm-tools` prints WAT, and Talos's WAT decoder produces the module value.  The theorem then needs a connection lemma stating that decoding the printed form of the emitted bytes yields a module with the expected shape, which drags `wasm-tools` (a Rust binary) and the WAT decoder into the proof pipeline for every fragment program.  A universally quantified theorem cannot run an external binary, so Option A in its literal form only supports per-artifact proofs, which is what exists today.

Option B constructs the Talos-model module value directly from the compiler's own module representation in `LeanExe/Wasm/Binary.lean`, as a Lean function from the compiler's `Module` to Talos's module type.  The theorem then speaks about `talosModule (emit ir)` with no external tools, and the byte-level artifact comparison remains a separate check that the shipped bytes match the modeled module (per artifact, exactly as the check scripts do now).  The cost is a translation function and the obligation that it agrees with the WAT-decode path on the artifacts we ship; the existing byte-for-byte check scripts already discharge that agreement empirically per case.

Recommendation: Option B.  It is the only form in which a universally quantified fragment theorem can be stated, and it shortens the trusted path by removing `wasm-tools` and the WAT decoder from the proof loop.  The decision affects the `CodeLib` dependency surface (the translation function needs Talos's module type as a library) and should be confirmed before implementation.

Superseding note, same day: the user restated that the project's point is proving correctness of what is actually executed, which resolves the emphasis.  The deliverable is a proved artifact, so the per-artifact pipeline scales first and the general theorems enter later as cost reducers.  The Option A versus B framing partially dissolves under that reading; what matters is that each artifact theorem binds to the shipped bytes, which the check scripts already enforce.

## 2026-07-06: Transactional update mode

`tools/check-talos-case.sh --update` now backs up the checked-in WASM, WAT, and generated `Program.lean`, replaces them with fresh compiler output, regenerates the model, rebuilds the proof, and restores the backups on any failure.  Previously a failed update left unvalidated proof inputs in the tree that a later plain check would silently accept.  Each wrapper passes a new `--program` flag naming its generated model file.  The failed-update path was exercised repeatedly during the byte-validator proof development below and restored the tree correctly every time.

## 2026-07-06: Talos proof for byte validation over memory

The fourth Talos artifact proof covers `LeanExe.Examples.AsciiDigits.validateGeneric`, the repository's original first-milestone program: `ByteArray -> Bool`, scanning input bytes in linear memory through a fuel loop.  It is the first artifact theorem over the memory model with universally quantified input.  `Project.Validate.Spec.validateGeneric_correct` states: for every byte list, every store whose memory holds those bytes at a pointer (the `BytesAt` hypothesis, matching the `load8U` rule's address form and bounds side condition), and every pointer, the generated export terminates and returns `1` exactly when all bytes are ASCII digits.  The proof has no `sorry`, no added axioms, and no `native_decide`.

The proof decomposes along the generated functions.  `func0` (the digit test) and `func1` (the guarded byte load) get small `TerminatesWith` lemmas; `func1` discharges the load's bounds check and read value against `BytesAt`.  `func2` (the fuel loop) uses `wp_loop_cons` with a two-arm invariant: either the scan is at position `i` with every byte below `i` a digit and fuel exactly `length + 1 - i`, or the done flag is set and the result local holds the answer.  The measure is `2 * fuel + doneFlag`, which decreases through the flag-setting iteration where fuel is unchanged.  The export wrapper composes with `wp_call_tw`.  The shared `ValidateSpec` in the example file instantiates both the plain-Lean theorem (`validateGeneric_correct` over `validateFuel`, proved by induction on fuel) and the Talos theorem, mirroring the association-list pattern.

Two mechanical lessons for the next memory proof.  First, `wp_run` stops at every `iff`; the working cadence is `refine wp_iff_cons rfl ?_` to peel, then `rw [if_pos/if_neg (by simp [hyp])]` to choose the branch, then `wp_run` again, with the deciding hypotheses (`fuel ≠ 0`, index-versus-length, digit-versus-not, no-wrap) proved up front.  Second, the heartbeat budget is cumulative per theorem: the three-path loop proof needs `set_option maxHeartbeats 64000000` where GCD needed 8000000, and the final arithmetic goals need the `UInt64.size`-to-literal rewrite before `omega` because `omega` treats `UInt64.size` as an opaque atom.

Checks run:

- [x] `tools/check-talos-validate.sh --update` built the proof with zero errors
- [x] `tools/check-talos.sh` over all four cases plus the aggregate `Project` build

## 2026-07-06: Abstract heap predicate and shared proof lemmas

The association-list proof no longer hard-codes cell addresses.  A new inductive predicate `ListSegAt st addr kvs` describes a linked association-list segment in memory: each cell holds a tag word `1`, the key, the value, and the tail pointer in consecutive 8-byte slots, the terminator holds tag `0`, and every read carries its bound.  The generated lookup function gets one lemma, `func0_seg`, proved by induction over the list: for every segment and every key, the export returns the first matching value or `0`.  The four per-node lemmas at addresses 4464, 4384, 4304, and 4224, and their per-node expected-value functions, are deleted; the only place concrete addresses remain is `sample_seg`, which shows the constructed sample is a segment at its root.  The public theorem `lookupDemo_correct` is unchanged in statement, and the lookup lemma now applies to arbitrary constructed lists, which is what the next list-building artifact will need.

`Project/Common.lean` now holds the lemmas the artifact proofs share: `size_eq`, `toNat_ofNat_lt`, `ofNat_inj`, `toNat_add_one`, and `getBang_eq` from the byte-validation proof, plus the address-form conversions `toUInt32_toNat`, `toUInt32_ofNat_mod_toNat`, and `toUInt32_eq_ofNat` that connect `(addr + c).toUInt32` hypotheses to the modular normal form `simp` produces in wp goals.  The mechanical lesson: `omega` treats `addr.toUInt32.toNat` and `addr.toNat % 4294967296` as unrelated atoms, so segment-style predicates must be rewritten into the goal's normal form before the bounds discharge, and the conversions belong in one place.

Checks run:

- [x] `tools/check-talos-assoc-list.sh` built the refactored proof with zero errors
- [x] `tools/check-talos.sh` over all four cases plus the aggregate `Project` build

## 2026-07-06: Talos proof for byte append through the allocator

The fifth Talos artifact proof covers `LeanExe.Examples.ByteArrayPrograms.appendBang`, the first memory-writing artifact.  `Project.AppendBang.Spec.appendBang_correct` states: from any store whose free list is empty, whose heap-top global leaves room for the rounded allocation within current memory, and whose input bytes sit below the heap top, the export terminates, returns the fresh pointer `g0 + 48` and `length + 1`, the result region holds the input bytes followed by `33`, and every byte below the old heap top is unchanged.  The proof has no `sorry`, no added axioms, and no `native_decide`, and it verifies the inlined runtime allocator on its bump path: the free-list walk exits on its first test, the pointer-wrap and memory-grow guards discharge from the fit hypotheses, and the six reference-count header stores land above the old heap top.

The copy loop uses a two-clause memory invariant: the number of bytes already copied into the result region, plus a frame clause that everything below the old heap top equals the pre-call memory.  The frame clause is also part of the public theorem, so the statement rules out corruption of the caller's input.  Pointwise write reasoning goes through two small local lemmas, `write8` at the hit address and `write8` away from it, with the hit stated as an equation hypothesis so the rewrite never touches the address expression itself; the six `write64` header stores use the same shape with a generic address.

Mechanical lessons beyond the validate proof.  First, `wp_run` stops on locals bookkeeping when the frame comes from an invariant; a plain `simp` after `wp_run` collapses it, and branch conditions surface as `if a ≥ b` in `GE` form, so the deciding facts must be supplied as `≥`-typed terms for `if_pos`/`if_neg`.  Second, `simp only [Mem.write64]` across a six-write chain exceeds the step limit because of the literal byte-extraction arms; unfolding is avoided entirely by the generic one-write frame lemma applied six times with the disequality proofs inline.  Third, `simp` normalizes `(UInt64.ofNat k + 1).toNat` to `(k + 1) % 2^64` on its own, so measure goals close with `omega` directly.

Checks run:

- [x] `tools/check-talos-append-bang.sh --update` built the proof with zero errors
- [x] `tools/check-talos.sh` over all five cases plus the aggregate `Project` build

## 2026-07-06: Shared write-frame lemmas

`Project/Common.lean` now holds `write8_bytes_ne`, `write8_bytes_hit`, and `write64_bytes_lo`, and the byte-append proof uses them instead of local copies.  The hit lemma takes the address as an equation hypothesis so the rewrite never touches the address expression, which is the form the copy-loop and exit-store steps need.

## 2026-07-06: Fold leak diagnosis

The leak accounting flagged `arrayFoldByteArrayAccumulatorReleaseStats` at 11 allocations against 2 frees.  The diagnosis from the generated binary: the entry contains nine inline allocation sites, and at runtime the source-level costs decompose as one allocation for the `#[65, 66, 67]` literal, one for the starting accumulator, and three per fold iteration, of which only one is the copy-on-write `push` itself.  A direct push chain costs exactly one allocation per push (`bytesABC` runs at 3 allocations, 2 releases, 2 frees, with each replaced fresh predecessor reclaimed), so the fold body introduces roughly two extra allocations per iteration: intermediates from materializing the accumulator value into and out of the callback.  The accumulator-replacement rule fires correctly (2 releases, matching the source-level counters) but sees none of the intermediates, the initial accumulator is skipped by the documented alias rule even though it is provably fresh here, the input array literal is never released despite being a fresh nonrecursive owner in a scalar-result function, and the final accumulator leaks after its last use.  The release-rule work should target the per-iteration intermediates first, since they dominate and are provably fresh and dead within one iteration.

## 2026-07-06: compile-wat diverges from the emitted binary

Comparing `compile-wat` output against `wasm-tools print` of the `compile` binary for the same entry shows two different programs.  The binary contains the reference-counted runtime: paired free-list and bump allocation paths with header writes at every inline allocation site, and counter increments that match the observed runtime statistics.  The `compile-wat` output contains a headerless bump allocator with no free list and no counters: `moduleWat` in `LeanExe/Wasm/Binary.lean` is a second, hand-written WAT backend with its own hard-coded runtime, and it has drifted from the binary emitter.  The Talos proof pipeline is unaffected because the check scripts print WAT from the binary with `wasm-tools`.  Anyone reading `compile-wat` output, and any future proof work that trusted it, would be reasoning about code that does not ship.  The fix is a design decision: either derive the WAT text from the same lowering as `moduleBytes`, or retire `compile-wat` and document `wasm-tools print` as the inspection path.

## 2026-07-06: compile-wat removed

The decision: remove `compile-wat` now, and restore text output later on top of a structured backend that serializes the same lowering as `moduleBytes`.  The whole hand-written WAT backend is deleted from `LeanExe/Wasm/Binary.lean`, about 2,300 lines, along with the `compile-wat` command.  The two size-regression tests that compiled WAT now measure the compiled binary instead, which is the artifact whose size matters, with thresholds recalibrated against current output (`arrayStructureReplicateHelperRead` at 2,001 bytes against a 20,000 limit; the two JSON transforms near 49 KB against 200,000).  The README, manual, and specification point inspection at `wasm-tools print` of the compiled binary.  The structured-backend refactor, which also gives the fragment theorem its subject, is scheduled as its own piece of work.

## 2026-07-06: structured backend

The emitters in `LeanExe/Wasm/Binary.lean` now build `List Instr` values, where `Instr` is a small inductive in `LeanExe/Wasm/Instr.lean` covering exactly the instructions the compiler emits: constants, local and global access, calls, i64 arithmetic and comparisons, the handful of i32 operations, loads and stores at the three widths, memory size and grow, and structured control flow (`block`, `loop`, typed `if` with optional `else`, `br`, `brIf`).  A total function `encodeInstr` serializes each constructor to the exact byte form the fused emitter produced, and it is the only place instruction opcodes live.  Instruction-building atoms (`i64Const`, `localGet`, and the rest) shadow the byte-level helpers inside the `CoreWasm` namespace, so the emitter code above the encoder reads as before while producing structured values.  Byte-level code remains in three places: the leb128 and section-framing helpers, the function-body wrappers (`bodyI` encodes a body's instructions and prepends its local declarations), and the early WASI prototype at the top of the file.

The gate for the refactor was byte identity.  Fresh compiles of `appendBang`, `matchBook`, `steps`, and `arrayFoldByteArrayAccumulatorReleaseStats` are byte-identical to binaries snapshotted before the refactor, `tools/check-talos.sh` confirms all five proof artifacts unchanged and rebuilds every proof, and the full test suite passes (301 standard comparison cases, 58 IR interpreter cases, 56 runtime cases).  The encoder compiles without `partial`, so later work can prove facts about it by induction; the next step on this line is a `printInstr` WAT printer over the same `Instr` values, which restores `compile-wat` as a second serializer of the one lowering.

## 2026-07-06: release path proved over the free list

The sixth Talos artifact covers the allocator's release path.  The subject is a new example, `pushBangSize`, chosen because the optimizer eliminates slice temporaries: `(input.push 33).size` is the smallest program whose generated code materializes a heap object and then discards it, so the entry contains the full inline allocator followed by `call $release` on the fresh raw object.  The case is `tools/check-talos-push-size.sh`, registered in the aggregate script and the Talos crate workspace as `push_size`.

The proof splits at the call.  `func4_frees_fresh_raw` is a self-contained theorem about the release function: for any store holding a nonzero raw object with refcount one at `p` (stated as three `read64` header facts), running function 4 on `[p]` terminates with the refcount slot cleared, the old free-list head written into the next-pointer slot, global 1 pointing at `p`, and the release and free counters advanced; the postcondition gives the exact final memory as a two-write chain and the exact globals as a three-set chain.  The main theorem re-proves the appendBang allocation prefix with the copy-loop invariant extended by four header `read64` facts (magic, refcount, capacity, kind), which the write-frame lemmas carry across each byte copy, and then consumes the release theorem through `wp_call_tw`.  The final statement: the export returns `length + 1`, the free list ends at the released object with its capacity slot intact and next pointer zero, alloc, release, and free counters each advance by one, retains stay untouched, and every byte below the old heap top is unchanged.  No sorry, no axioms, no native_decide.

`Project/Common.lean` gains the word-granularity frame lemmas this needed: `write64_bytes_ne` (two-sided window disjointness), `read64_congr`, `read64_write64_ne`, `read64_write8_ne`, and `write8_pages`.  CodeLib's `Mem.read64_write64_same` supplies the read-after-write case.

## 2026-07-06: array literals allocate once

The fold-leak work started from the recorded diagnosis, and the new `dump-ir` command (a `reprStr` dump of the compiled IR module, added to the CLI next to `ownership-report`) immediately corrected it.  `arrayFoldByteArrayAccumulatorReleaseStats` had no per-iteration callback intermediates: its eleven allocations were two full constructions of the `#[65, 66, 67]` literal, four allocations each, plus one copy-on-write push per iteration.  The literal lowering built `arrayAllocSlots` followed by one copying `arraySetSlots` per element, and the fold's elaborated default stop bound `as.size` re-extracted the whole literal a second time.

Three compiler changes remove the waste at its source.  First, a new IR expression `arrayLiteralSlots width childMask elements` allocates once and stores each element's slots directly, with per-element owned masks deciding transfer against retain; `List.toArray` extraction now produces it instead of the set chain.  Second, fold extraction binds a non-local array expression to a fresh local, folds over the local, and reads the default stop bound from it, recognizing `Array.size` of the same source term; the letE-wrapped fold value converts to a preceding assign plus the existing fold-assign statement.  Third, ownership transfer inside a literal is consume-once: an owned local transfers at its first occurrence across the literal's slots and is retained at later ones, in both the extraction-time mask computation and the alloc-time mask refresh.  The first test run caught the need for this rule as a refcount underflow trap in `u64BinarySharedArrayScore`, whose literal stores the same child twice; the old set chain had masked the double transfer with its copy-time retains.

The measured entry drops from eleven allocations to four: one literal, three pushes, with releases and frees unchanged at two.  Three recorded expectations moved because the leaked set copies had held stale retains that kept children alive past their release: `optionByteArrayArrayRuntimeReleaseFrees` and `publicTokenArrayRuntimeReleaseFrees` gain one free (302 to 303), and `byteArrayGroupArrayRuntimeReleaseFrees` now tears its six-object tree down completely (403 to 606).  All 784 correctness cases, the comparison suites, and all six Talos artifact checks pass; the artifacts are byte-identical because none of the proved programs contains an array literal.  The remaining fold leaks are the input literal and the final accumulator, both single objects per fold.

## 2026-07-07: fold source and result released

The two remaining fold leaks close.  When fold extraction binds a constructed source array to a local, the fold-assign conversion now appends a release of that local after the loop, guarded by `exprBuildsFreshArray`, a conservative allowlist of array-constructing expressions that keeps the previous leak instead of risking a double release on anything it does not recognize.  The final accumulator closes through classification: `exprReturnsOwnedNonrecursiveHeapObjectFrom` now recognizes a fold value at an offset in its `releaseOffsets` as owned, provided the initial accumulator at that offset is itself owned or the null pointer, so the existing owned-temp release machinery frees the result after its last use.  The zero-iteration case motivates the init condition: a fold that never runs returns its initial accumulator, and releasing a borrowed init would corrupt.

The measured entry is now leak-free at four allocations, four frees, zero retains.  Six recorded expectations move by exactly the released input literal entering the measured window (30202 to 30303 and analogues), and the call-stats quad for the measured entry goes from 4/0/2/2 to 4/0/4/4.  All suites and all six Talos artifact checks pass with byte-identical artifacts.

## 2026-07-07: compile-wat restored as a second serializer

The `compile-wat` command returns on top of the structured backend.  `LeanExe/Wasm/Wat.lean` prints the module as WAT text: `instrLines` maps each `Instr` constructor to its text mnemonic, and the module skeleton (types, memory, globals, exports, function frames) mirrors the section builders in `Binary.lean`.  The function bodies come from the identical `List Instr` values the byte encoder serializes, factored out as `emitFuncInstrs` and `coreAllocInstrs`, `coreResetInstrs`, `coreRetainInstrs`, and `coreReleaseInstrs`; the byte bodies wrap the same lists, so the refactor is byte-preserving by construction and the artifact checks confirm it.

The gate is stronger than the old backend ever had: `tools/check-wat.sh` compiles nine entries (the six Talos programs, the measured fold entry, and a JSON transform), parses each `compile-wat` output back to a binary with `wasm-tools parse`, and requires byte identity with the `compile` output.  All nine match exactly, which pins not just semantics but section layout and LEB encoding.  The one fix the gate demanded was multi-result signatures: `matchBook`'s helper returns three values and the first draft printed at most one.  The README, manual, and specification present `compile-wat` as the inspection path again, with `wasm-tools print` as an independent view.

## 2026-07-07: free-list reuse case blocked on helper releases

The planned seventh Talos artifact needs a program that releases a raw object and then allocates again, so the allocator takes the free-list unlink path.  Three candidate shapes all fail to produce the release-then-allocate sequence.  A let-bound `(input.push 33).size` never releases the temporary: the owned-temp release machinery in `materializeResultValue` and `assignResultExprWithOwnedReleases` fires only on the top-level result value, and an intermediate scalar assign gets no releases.  The operand-nested form `(input.push 33).size + (input.push 34).size` fails the same way: the owned temporaries sit inside the operands of the result's `u64Bin`, and only top-level `letE`, `letLets`, and `letCall` shapes carry releases.  The composed form `pushBangSize input + pushBangSize input` compiles the helper without any release at all: `pushBangSize` as an entry contains `call $release` (the proved push_size artifact), but the same definition compiled as a helper in this module contains no calls, so the two temporaries leak and the second allocation extends the heap instead of reusing the freed node.

The entry-versus-helper difference is the item to fix first: both routes reach `materializeResultValue`, so the divergence is in how the helper's result value is shaped or flagged when it arrives there (`useAbi` differs between the paths).  Diagnosing that is the next step; the reuse artifact and its proof follow once a shape exists whose second allocation observes a nonempty free list.

## 2026-07-07: helpers release owned temporaries

The entry-versus-helper divergence is fixed.  In `materializeResultValue`'s fallback arm, the internal-ABI path converted a `LocalLet` holding a nested `letE` chain into one plain assignment, and the ownedness check saw only what the whole expression returns, so owned intermediates inside the chain never released.  The exported-ABI path flattens the same chain through `assignResultExprWithOwnedReleases`, which releases owned intermediate bindings.  The fallback arm now converts `.expr` and `.slots` lets through that same flattening (keeping the fold-assign conversion for fold-shaped slots), so helpers get the identical release discipline.  `pushTwiceSizes`, which calls `pushBangSize` twice, runs leak-free at two allocations, two releases, two frees, and its second allocation reuses the freed node from the first call's release.  The full suite passes with no expectation changes and all six Talos artifacts stay byte-identical, so no existing program shape was affected.

## 2026-07-07: free-list reuse proved

The seventh Talos artifact covers the allocator's unlink path.  `pushTwiceSizes` calls the compiled `pushBangSize` helper twice; with the helper-release fix in place, the first call's released temporary sits on the free list when the second call allocates, and the search loop takes the node instead of extending the heap.  The proof splits the helper's two behaviours into separate theorems over function 0.  `func0_empty` restates the push_size result for this module: bump allocation, with the released node's capacity and next pointer exposed for the caller.  `func0_reuse` is the new work: its free-list walk runs two iterations under a disjunctive invariant, the first taking the head node through the capacity test, the unlink store to global 1, and the header reinitialization, the second exiting on the result-local test; the copy loop then runs under a reuse variant of the invariant whose allocator state is the post-unlink state.  The release function's raw path is `func5_frees_fresh_raw`, the push_size theorem retargeted at this module's function table.

The entry theorem composes the two helper theorems through `wp_call_tw`, rebuilding the input `BytesAt` for the second call from the first call's below-heap frame, and discharges the result overflow guard.  The statement pins the reuse fact directly: the final heap top is `g0 + 48 + allocSize`, one rounded allocation above the initial top, while the alloc, release, and free counters each advance by two and the free list ends back at the reused node.  No sorry, no axioms, no native_decide.  All seven artifact checks pass.

## 2026-07-07: transfer accounting fixed for returned containers

The retain-artifact program exposed an ownership undercount.  `sharedPushPair` binds one push result and returns `#[appended, appended]`: the literal transfers the local at its first occurrence and retains it at the second, so the refcount must end at two.  The compiler emitted an additional guarded release of the local, leaving two live references backed by a count of one; the unshared `#[appended]` variant showed the same spurious release, dropping the sole reference to zero while the returned array still pointed at it.  The cause: the owned-temp release decisions in `materializeResultValue` consult the pre-materialization value view, whose literal owner masks are still empty, so the transfer of the local is invisible; the masks are refreshed with owner sources only during materialization.  The set-chain lowering had the same blind spot, untested because no existing case returned a container holding a let-bound owned local.

The fix reads the answer from what actually ships: a new `stmtReleasedSlots` scans the materialized body statement, which carries the refreshed masks, and the release decisions in the `letE` and `letLocal` arms now consult it alongside the value view; the flatten fallback also refreshes owner masks before its release accounting.  Both program variants now end with exact counts, and `free` on the returned array performs the full recursive teardown to refcount zero.  The full suite passes with no expectation changes and all seven Talos artifacts stay byte-identical.

## 2026-07-07: the inline retain sequence proved

The eighth Talos artifact is complete.  `sharedPushPair` builds `input ++ [33]` once and returns `#[appended, appended]`; the theorem proves that the returned array's cells alias the single temporary, its refcount ends at exactly two, the retain counter advances by one, the alloc counter by two, and everything below the old heap top is unchanged.  This is the first proof over the inline retain sequence the compiler emits for shared children: the magic check against a header the same proof wrote two allocations earlier, the refcount load, the counter increment, and the read-modify-write store from one to two.

Three mechanical lessons paid for the proof.  First, once the store carries the phase-two write chain, the standard `wp_run` simp set exceeds its step budget; a local `wp_run_big` macro with a ten-million-step limit replaces it, and a `set stB` binder folds the bang-written store to keep terms small.  Second, mixed address normal forms are the main hazard in a two-allocation proof: the `% 2^64` layer from heap-pointer sums needs one `Nat.mod_eq_of_lt` normalization before frame lemmas apply, offset subtractions must be reduced to literals eagerly (an unevaluated `UInt64.toNat 8` turns every omega atom opaque), and `(0 : UInt64).toNat` needs its `rfl` like every other literal.  Third, `simp only` with a hypothesis whose left-hand side is a thirteen-write chain fails to match where plain `rw` succeeds, so the big read-back facts rewrite with `rw`.  No sorry, no axioms, no native_decide; all eight artifact checks and the full test suite pass.

## 2026-07-07: recursive release proved through the array branch

The ninth Talos artifact closes the release function's coverage.  `sharedPairFreeStats` builds the shared pair through the compiled helper and releases it; the entry theorem pins the measured value at the literal 302, three releases and two frees, plus the free-list head and all four counters.  The recursion turned out not to need a measure-carrying `FuncSpec`: the object graph is depth two and the child states at the two recursive call sites are concrete, so `func7_frees_pair`, the array-branch theorem, consumes two leaf lemmas through `wp_call_tw` — `func7_decrements` for the first call, which lowers the shared child from two to one in a single store, and the raw-free lemma for the second, which puts the child on the free list.  The cell walk itself runs under nested loop invariants: a three-state outer disjunction indexed by the item, each step opening an inner four-state invariant over the slot, with the store equations evolving at the two call sites.  Composition order in the final state is exact: child at refcount zero, parent freed in front of it, free list reading parent then child.

The helper's construction theorem is the SharedPair proof ported to this module's local numbering, which a mechanical stream alignment of the two generated programs produced (one extra result temporary, everything else shifted), with the postcondition extended to the eleven header and cell facts the array branch reads.  New mechanical lessons: `simp` normalizes same-index `List.set` chains during invariant establishment, so invariants written as raw set-compositions bridge by `List.set_set`; counter cancellations over symbolic globals (`g4 + 1 + 1 + 1 - g4 = 3`) close by `bv_decide`; and a goal-side `rw` succeeds where `simp only` fails to index large chain hypotheses, as in the retain proof.  No sorry, no axioms, no native_decide.  All nine artifact checks and the full test suite pass.

## 2026-07-07: owned temporaries release in every statement position

The last two known temporary-leak shapes close.  Let-bound temporaries (`let first := (input.push 33).size` never released the push) now flatten through the release-aware assigner: the `letLocal` result arm and the internal-ABI fallback both convert their materialization lets with a shared `localLetStmtWithOwnedReleases`.  Operand-nested temporaries (`(input.push 33).size + (input.push 34).size`, where both pushes hide inside the operands of the result's addition) close through a new `exprSpineOwnedTemps` traversal: the plain-assign fallback of `assignResultExprWithOwnedReleases` collects owned `letE` binders along the expression spine — nested lets, both operands of scalar binary operations, and both branches of a conditional, which is safe because locals are zero-initialized and releasing null is a no-op — and appends guarded releases for those the expression neither consumes nor returns.  Both shapes now run at two allocations, two releases, two frees, with the second allocation reusing the first's freed node.  All nine proof artifacts stay byte-identical and the full suite passes unchanged.

## 2026-07-07: byteArray folds share and release their constructed source

The byteArray fold had the analog of the array-fold source duplication, worse by one: `wrapExprLets` wrapped the same construction lets around the pointer view, the length view, and the elaborated default stop bound, so a fold over a constructed byte array built its source three times and freed none of them.  The measured `foldFreshSum` ran at six allocations and zero frees.  Three changes close it: the fold value wraps the parts lets once around the whole fold expression instead of once per view; the elaborated default stop bound `b.size` on the same source term reuses the shared length; and the fold-assign conversion peels the value-let wrapper into hoisted assignments, converts the fold, and appends releases for wrapper binders that construct fresh objects.  The entry now runs at two allocations, two releases, two frees.  One recorded expectation moves for the same reason as before, the freed source entering the measured window (`byteArrayFoldByteArrayAccumulatorReleaseStats`, 30202 to 30404).  All nine artifacts stay byte-identical (parameter-sourced folds have empty wrapper lets and identical output) and the full suite passes.

## 2026-07-07: slots-release case blocked on flatten duplication

The tenth artifact was to cover the release function's slots branch through `chainFreeStats`, which builds a one-link recursive chain holding a pushed byte array and releases it.  The measured entry runs at five allocations against an ideal three: the constructor's slot values each embed a complete copy of the payload construction, so the push executes twice, and the extra copy leaks.  The cause is structural: `ByteArray.push` extraction correctly produces a value-level `letE` chain binding the construction once, but `flattenInternalValue`'s `letE`, `letCall`, and `letLocal` arms replicate the wrapper onto every flattened slot (`flattened.map (fun expr => .letE slot value expr)`), so any consumer that evaluates all slots — constructor materialization through `heapAllocSlots`, fold initial accumulators, and the rest — re-evaluates the binding once per slot.  The fold-specific fixes to date worked around exactly this at two call sites; the general repair is to route multi-slot consumers through the lets-materializing path (`materializeInternalValueLets`) instead of the expression-list flattening, which is an extraction refactor with a wide blast radius.  The slots-release proof waits on that fix: pinning an artifact over duplicated construction would certify code the repair is about to change.  The `chainFreeStats` example stays as the measured reproduction, at releases three and frees three against five allocations.

## 2026-07-08: slots-kind release proved

The tenth Talos artifact covers the release function's slots branch.  With correctness and simplicity ahead of the flatten repair, the subject sidesteps the duplication entirely: `boxFreeStats` builds a `UBox` chain (`node 1 7 nil`) whose slot values are scalars and a child pointer, so no construction wrapper exists to duplicate, and the shipped code is already the code worth certifying.  The entry theorem pins the measured value at the literal 202: two releases and two frees, with the free-list head at the node, both headers zeroed at the refcount word, and all four counters exact.

The release side is two lemmas over function 6.  `func6_frees_leaf` walks the three slots of the nil box under a four-state invariant, calls itself on the null slot through `func6_null` (the p = 0 early return), and frees the box.  `func6_frees_node` runs the same walk on the node, meets the live child pointer at slot two, and consumes the leaf lemma through `wp_call_tw` under a separation hypothesis keeping the child's header out of the parent's write frame.  The entry side hit an elaboration wall: the phase-two goal carries the phase-one nine-write chain in the store, and elaborating the whole entry in one theorem exceeded eleven gigabytes.  The repair is a cut: a private `boxPhase2` definition names the instruction suffix from the second allocation's free-list walk onward, and `boxPhase2_spec` proves it against a store described only by the read facts phase two needs — six header reads, six globals, and the page bound — so the write chain never enters the helper's elaboration.

Two composition lessons from the cut.  First, the helper's postcondition must be stated in the simp-normal form the entry goal reaches, not the library's `take ++ drop` form; even then the two match-expressions elaborate to distinct matcher constants that `refine` will not identify, and `wp.imp` — apply the helper, then discharge the postcondition implication by `cases c <;> exact h`, under which both matchers reduce — composes where direct application fails.  Second, the read facts bridge from the write chain by peeling `read64_write64_ne` frames outermost-in to the hit, with one `omega` rewrite collapsing the `% 2^64` layer on the slot addresses.  No sorry, no axioms, no native_decide.  All ten artifact checks and the full test suite pass.

## 2026-07-08: runtime lemmas proved once, consumed everywhere

The per-artifact cost survey confirmed the runtime suite is uniform: every generated module ends with the same four functions — allocate, reset, retain, release — byte-identical across all ten modules except for release, whose two recursive call sites embed its own function index.  That uniformity picks the mechanism for reusable lemmas without touching the compiler or any shipped binary: `Project/Runtime` now holds the shared instruction streams (`releaseBody` parametrized by its index), forty `rfl` checks pinning every module's runtime functions to them, and module-generic specifications taking the module and function index as parameters, with the lookup hypothesis each artifact discharges by `rfl`.

Four lemmas moved: `retain_spec`, `release_null`, `release_decrements`, and `release_frees_fresh_raw`.  The generic proofs are the concrete proofs nearly verbatim — the entry step passes the lookup and import hypotheses to `of_wp_entry_for` instead of computing them from the module constant, and no other step consults the module because the leaf paths never reach a call.  The five concrete copies across SharedPair, BoxFree, PairFree, PushSize, and PushTwice became one-line instantiations under their old names, so no call site changed: 517 lines of duplicated proof deleted for 24 lines of application.  A new program's proof now gets retain and the three release leaf behaviors for free; the recursive release branches remain per-shape, consuming these leaves through the call rule.  All ten artifacts prove unchanged.

## 2026-07-08: the frame-peeling boilerplate becomes a tactic

The read-over-write-chain derivation was the most repeated proof text: every header fact peels disjoint `read64_write64_ne` frames outermost-in with an omega side condition each, then lands on the syntactic hit.  `read_frames` in Common does exactly that as a `repeat first` loop, trying the hit lemma before each peel, so a stated read fact needs one word instead of a generated block; the sixteen peel blocks in the BoxFree spec, previously emitted by a script, are now single calls.  The stopping behavior is safe by construction: at the hit the separation omega fails and the loop halts, and an opaque base store matches neither lemma.  Alongside it, `toNat_sub_le` generalizes the subtraction bridge every proof re-derived as a local have; the general form needs the explicit `toNat_lt_size` bounds the local instances got from literal hypotheses in context.  All ten artifacts prove unchanged on top.

## 2026-07-08: fold_sum, the first artifact on the consolidated infrastructure

The eleventh Talos artifact validates the economics the runtime consolidation and the tactic layer were built for.  `foldSum` folds byte addition over its input; the theorem is input-generic in the strongest sense available: for every input byte list, the compiled export returns the value of the source-level fold and leaves the store untouched.  The loop invariant carries the fold over the consumed prefix, two ordinary list lemmas (`sumTake_succ`, `sumTake_le`) connect the prefix sum to the full fold and bound it below the wrap threshold, and the compiled overflow guard — the source addition is on `Nat`, so the compiler emits a trap on wrap — discharges against that bound.

The measured cost confirms the direction: the complete spec is 203 lines including the statement, the invariant, and both list lemmas, against 526 for push_size, the nearest comparable artifact, and it needed no per-proof lemma about the runtime because the entry never allocates.  The proof took four build iterations from skeleton to closed, each fixing one form mismatch.  All eleven artifact checks and the full suite pass.

## 2026-07-08: constructor fields evaluate once

The flatten duplication is fixed at its consumers.  `flattenInternalValue` replicates a field's value-level let wrappers onto every flattened slot, so a heap constructor whose field carried a construction chain re-evaluated the chain once per slot; a `ByteChain` node holding a pushed byte array executed the push three times, leaking two copies.  The repair peels each constructor field's wrapper chain before flattening (`stripExtractedValueWrappers`, threading the owner-source context each wrapper induces), flattens the residue, and re-wraps the chain once around the whole `heapAllocSlots` expression, at all three allocation sites: the internal flatten, the ABI flatten, and the array-element flatten.  A field without wrappers takes the byte-identical old path, so all eleven pinned artifacts are unchanged.

The reproduction confirms the fix statically and dynamically: the `chainFreeStats` module drops from 1818 to 1324 lines of text format — the two extra copies of the push construction gone — and the measured value stays exactly three releases and three frees, so the hoisted ownership masks are still exact.  Alloc-delta measurement inside the example turned out to be impossible: Lean's compiler folds two `allocCount` reads that bracket pure construction code into one, since the construction is pure at the Lean level; counter deltas only survive across opaque runtime calls, which is why the recorded expectations encode output size instead.  Deeper nesting — a field that is itself a product whose components carry wrappers — still replicates inside the residue and remains open.  The full suite and all artifact checks pass.

## 2026-07-08: release-tree model

`Project/Runtime/Tree.lean` models the object graphs the release function tears down, the base for a generic recursive-release theorem.  A `RelTree` is a slots-kind object at refcount one whose masked slots hold null, an owned subtree, or a shared object the walk only decrements; scalars fill the unmasked slots.  The first version keeps three restrictions: slots-kind only (arrays stay per-shape), all node addresses distinct (no aliased shared leaves inside one release), and shared objects as leaves.  `TreeAt` ties a tree to a memory through the header, mask, and slot-word reads the walk performs; `RelTree.events` lists the walk's writes in traversal order — children before their parent, so the free list ends at the root; `applyEvents` folds those writes over a memory and the free-list head, and `footprint` with `footprintOk` carries the per-node regions and their pairwise disjointness for the frame lemmas.  The staged plan: read stability under `applyEvents` outside the events' regions, `TreeAt` framing by mutual induction, then the release theorem by structural induction consuming the recursive calls through the call rule.

## 2026-07-08: the release-tree frame theorem

The frame infrastructure for the generic teardown theorem is proved.  `read64_applyEvents_ne` shows an eight-byte read separated from every event's header region passes through the whole event fold unchanged, and `applyEvents_pages` preserves the page count.  On top of them, `TreeAt_applyEvents` and `SlotsAt_applyEvents` show a tree's entire shape — headers, mask, slot words, and child subtrees — survives any event fold whose regions avoid the tree's footprint.  Two structural decisions came out of failed attempts: the shape predicates are mutual inductive predicates rather than recursive definitions, because destructuring a match-compiled recursive `Prop` tripped a kernel-level type mismatch in the elaborated term, and the mutual induction runs on an explicit size fuel rather than Lean's mutual well-founded recursion, which hit the same kernel error through tactic-mode `cases` on the decreasing argument.  What remains for the theorem is the walk itself: the loop invariant over the slot index with the prefix of events applied, the recursive call consuming the induction hypothesis through the call rule, and the composition of the event folds.

## 2026-07-08: event containment and composition lemmas

The remaining supports for the teardown theorem's walk: `applyEvents_append` composes event folds over concatenation; `regionSub` with `regionsDisjoint_of_sub` transfers disjointness through containment; `events_sub` (fuel induction again) places every event's header region inside a footprint region of its own subtree, and `events_bounds` derives the pointer bounds from the footprint bounds.  Together with the frame theorem these give the walk proof everything it consumes: sibling disjointness pushes each child's events away from every other region, so headers stay readable and untouched subtrees stay intact as the loop advances.

## 2026-07-08: mask bits characterized

`natMask` computes the mask word the compiler stores for a slot list, and `natMask_testBit` identifies bit `k` with whether slot `k` is masked — the fact the walk's shift-and-test branch condition reduces to.  `natMask_lt` bounds the mask below `2 ^ length` for the shift arithmetic.  With these, every support the generic walk proof consumes exists; the walk theorem itself — the wp induction over the tree with the slot-loop invariant carrying the prefix of applied events — is the remaining piece.

## 2026-07-08: walk preamble proved

`TreeSpec.lean` holds the per-iteration facts for the generic walk: `slotsMask_shift_and` reduces the compiled shift-and-test branch condition on the stored mask word to the slot's kind, through the `Nat.testBit` characterization and the 64-bit shift semantics; `SlotsAt_get` indexes a slot predicate to the k-th read fact and child shape; `sizeOf_child_lt` feeds the fuel induction.  The walk theorem itself is what remains: the wp induction over the tree, with the loop invariant carrying the prefix of applied events and the recursive call consuming the induction hypothesis through the call rule.

## 2026-07-08: the generic teardown theorem proved

`release_frees_tree` closes the largest open item in the runtime lemma library: for any module carrying the shared release function, releasing the root of an ownership tree frees every owned node in traversal order, decrements every shared leaf, and leaves the free list at the root, with the release and free counters exact and every other global untouched.  The statement quantifies over the tree, so a new program's recursive teardown proof reduces to exhibiting `TreeAt`, footprint disjointness, and the page bound — no per-shape walk proofs.

The proof is a fuel induction whose node case runs the release prologue generically, then the slot loop under an invariant carrying the prefix of applied events: at slot `k` the memory is the event fold of the first `k` slots' teardowns, the counters have advanced by the prefix sums, and the free-list head is the fold's second component.  Each masked slot dispatches on its kind — a scalar skips, a null consumes the generic null lemma, a shared leaf would consume the decrement lemma through the same path, and an owned child consumes the induction hypothesis through the call rule, with the frame theorem lifting the child's shape over the earlier siblings' events and the footprint decomposition supplying the disjointness.  The exit branch skips the array arm and composes the parent's own free event onto the prefix through `applyEvents_append`.  Mechanical lessons: simp reshapes an invariant proposition between the loop lemma and the re-establishment goal, so the tuple must match the reshaped form; equation-style `rfl` lemmas beat simp on fold unfoldings; and counter arithmetic over `UInt64.ofNat` closes by injectivity into `Nat` with omega once the literal `toNat`s are evaluated.  No sorry, no axioms; the whole proof library builds.

## 2026-07-08: documentation overhaul

The verification documentation caught up with the work.  The proofs workspace README now describes the current architecture — the pinned runtime suite, the module-generic lemma library, the tactic layer, the release-tree model with the teardown theorem, and the two statement templates — with a complete eleven-artifact table replacing the five-artifact one.  A new top-level guide, `verifying.md`, records the end-to-end recipe for verifying a program, from source through scaffolding, runtime pins, statement, proof, and gates, with `fold_sum` as the worked example.  `agenda.md` was rewritten around the actually open work: a demand-driving target program, retiring the per-shape teardown proofs by lifting the tree theorem's restrictions, the fragment-level lowering theorem, the remaining compiler simplifications, and proof-layer ergonomics.  `summary.md`'s module inventory reflects the backend split and current line counts, its verification section describes the library organization, and its observations section drops the items this session closed.  The root README's Talos section defers to the workspace table instead of duplicating a stale copy.

## 2026-07-08: the compiler's LEB128 core compiles itself

First milestone on the `self-emit` branch.  `LeanExe/Wasm/Leb.lean` holds the LEB128 encoders inside the accepted subset: mutable `ByteArray` loops in `Id.run`, ten bounded iterations, and an arithmetic shift built from bit operations, since the subset has no `Int`.  The native encoder in `Binary.lean` now calls these definitions through thin wrappers — an `intBits` bridge converts its signed `Int` interface to the two's-complement bit pattern — so the shipped compiler and the self-compiled artifact run the same code.  The swap is byte-exact: all eleven Talos artifacts compare identical and the full suite passes untouched.

`test/self_emit.js` states the fixed point: the compiler compiles its own encoder to WASM, and the artifact's output equals an independent JavaScript reference over thirty-nine boundary values covering the full unsigned range, the seven-bit group edges, and the signed termination conditions on both sides of zero.  The next slices move outward through the encoder: the vector and section combinators, then instruction encoding, with a Talos proof of the LEB artifact as the verification target.

## 2026-07-08: the compiler's encoder self-compiles; its proof is partway

The `self-emit` branch reaches the milestone it set out for: the compiler's own WASM byte encoder, compiled by the compiler, produces the same bytes as the compiler emits natively.  `LeanExe/Wasm/Leb.lean` holds the LEB128 encoders and the vector and section combinators inside the accepted subset, written as fuel recursion over mutable `ByteArray` loops; the native encoder in `Binary.lean` calls these same definitions, so the shipped compiler and the self-compiled artifact run identical code.  Both swaps are byte-exact: all eleven prior Talos artifacts compare identical and the full suite passes.  `test/self_emit.js` states the fixed point — the self-compiled `u32lebU64` and `s64lebU64` artifacts match an independent reference over sixty-three boundary values spanning the seven-bit group edges and the signed termination conditions, and the vector and section combinators likewise.  This is the self-hosting result: a nontrivial part of the compiler's back end verified by running as one of its own outputs.

The Talos proof of that artifact is partway.  `LeanExe/Wasm/LebTheorems.lean` proves `u32lebU64_eq_lebList`, identifying the shipped encoder with a pure recursion by fuel induction.  In the proof workspace, `Project/LebU32` carries the artifact model, the runtime pins, and the sorry-free step lemmas: `copyStepPos` (one byte-copy iteration), `tailStepPos` (the final-byte store re-establishing the loop invariant in the done state), and the pos-branch iteration scaffold in `Iter.lean`.  The 8-byte-uniform-capacity bump allocation, the empty-free-list walk, the six header stores, and the copy loop are all discharged.  What remains is the continuation-byte branch — the mirror of the final-byte path, re-establishing the invariant with the running flag and `v / 128` — and the export wrapper over `func1`, then `func0_encodes` composes them into the statement that the export returns a pointer to exactly `lebList 10 n`.  The byte-identity check gates the self-compiled artifact; the full correctness theorem is deferred, not abandoned.

## 2026-07-09: the self-compiled LEB128 encoder is proved correct

The twelfth Talos artifact closes the self-hosting loop.  `u32lebU64_correct` states that the compiler's own unsigned LEB128 encoder, compiled by the compiler, returns for every `n` below `2 ^ 32` a pointer to a buffer holding exactly the bytes of `lebList 10 n`, together with its length, leaving every byte below the old heap top unchanged.  `LeanExe/Wasm/LebTheorems.lean` proves the shipped source encoder equal to that same `lebList`, so the two compose: the WASM the compiler emits for its own encoder computes the encoder.  No sorry; the axiom set is `propext`, `Classical.choice`, `Quot.sound`.

The proof is four sorry-free lemmas over the generated model.  `copyStepPos` and `copyStepNeg` discharge one iteration of the buffer copy.  `posIterLemma` and `negIterLemma` each prove one iteration of the compiled fuel loop -- the eight-byte-uniform bump allocation, the empty-free-list walk, the six header stores, the copy loop, and the byte store -- differing only in the emitted byte and in whether the loop invariant is re-established in the done state or the running state (fuel decremented, `v` replaced by `v / 128`).  `func0_encodes` runs the outer loop under `lInv`, dispatching on the rest test to one lemma or the other, and `u32lebU64_correct` composes the export wrapper through the call rule.

The proof found nothing wrong with the compiler or the emitted artifact.  It cost two mistakes of my own, recorded here because both are easy to repeat.  First, I defined `posProg` and `negProg` as the selector's then- and else-blocks with a trailing `.br 0`.  `wp_iff_cons` runs the chosen block alone under a continuation that handles the remaining instructions, so the branch programs must exclude the `.br 0`, and each iteration lemma's final obligation is a `Fallthrough`, not a `Break 0`.  The lemmas proved under the wrong definitions were true statements about the wrong programs, so they simply would not apply.  Second, I claimed Lean was behaving nondeterministically.  It was not: six builds from a fully-clean olean set are byte-identical.  The divergence came from rebuilding one olean while leaving a stale sibling whose lemma statement had since changed.  The real obstacle underneath is ordinary and documented: `exact` and `change` check definitional equality at bounded transparency and will not unfold a `def` down through `wp` and `exec`, so a lemma stated over a program name cannot be matched against a `wp_run`-reduced goal.  State the lemma so no such bridge is needed.

One performance lesson: proving `(g0.toNat + 56 * j + 48 + j) % 4294967296 = g0.toNat + 56 * j + 48 + j` with `by omega` inside a `rw [show ...]` dominated `posIterLemma`'s elaboration.  Hoisting the bound as a hypothesis and rewriting with `Nat.mod_eq_of_lt` took the file from exceeding four million heartbeats to seventy-eight seconds.

## 2026-07-09: a CLOB kernel from scratch, compiled and scaffolded for proof

`LeanExe/Examples/Clob.lean` is a central-limit-order-book kernel written from scratch in the accepted subset, shaped for proofs: fuel recursion for the maker search and the matching loop instead of `Id.run` for-loops, a flat `Array Order` book in time order, and scalar `UInt64` fields throughout.  Operations: `postOnly`, `limit`, `market`, `cancel`, `quote`, and `depth`, plus a scalar `scenario` entry that runs a fixed operation sequence and folds every result into a checksum.  Matching preserves FIFO among equal prices by keeping the first index on ties, skips same-trader makers, and treats market orders as price-unlimited.  The leanclob kernel served as a design reference; no code was ported.

`LeanExe/Examples/ClobTest.lean` holds the source-level guards: branch behavior for all four statuses, partial and full fills, FIFO on price ties, same-trader skipping, quote aggregation at the best price, and depth aggregation per side.  `report` classifies every entry as implemented by the first generic compiler fragment, and all seven entries compile.  Differential checks pass: `compare-standard --mode pure` matches on six `scenario` seeds, and `--mode pure-abi` matches `cancel` through the public array-of-structures ABI.  Two harness details worth remembering: with `--abi-arg` present the harness ignores `--arg`, so scalars also travel as `--abi-arg`, and structure values in `--abi-arg` and the serializer are JSON objects keyed by field name.

The thirteenth Talos case is scaffolded as `clob_quote`: `quote` reads the book and returns six scalars, so it exercises the array-of-structures input without heap results.  The artifact is pinned, the model is generated, and the runtime pins hold by `rfl` (`func11` through `func14`, release at index 14).  The export takes one `i64` (the book pointer) and returns six `i64` values.  The proof needs one new piece of machinery: a segment predicate for an array of five-slot structures in memory, the `ListSegAt` pattern from `assoc_list` lifted to fixed-width elements, with the loop invariant carrying the source fold over the consumed prefix.  Statement and proof are the next work.

- [x] Kernel builds; guards pass.
- [x] All entries compile; `scenario` and `cancel` match standard Lean.
- [x] `clob_quote` case scaffolded, pinned, model generated, runtime pinned.
- [x] `ClobQuote` spec stated and proved.
- [ ] Artifact theorems for `cancel`, `postOnly`, then `limit`.

## 2026-07-09: the thirteenth artifact: `quote` over every book in memory

`Project.ClobQuote.Spec.quote_correct` is proved, sorry-free, on the standard
axiom set (`propext`, `Classical.choice`, `Quot.sound`).  The statement: for
every order list laid out in memory as a length word followed by five words
per element, the compiled `quote` export returns the six fields of the source
fold and leaves the store untouched.  This is the first input-generic theorem
over an array-of-structures input.  `tools/check-talos.sh` passes for all
thirteen cases, and the differential suite passes untouched.

The proof splits into three modules.  `Step.lean` proves `func9`, the
compiled `quoteStep`: a pure 770-instruction branch tree that recomputes the
branch conditions once per output field.  The proof case-splits on the eight
source-level leaves and walks each with a `wp_step` macro that peels one
`iff`, decides every `ite` in its condition by `split` with contradictory
branches killed by `exfalso; simp_all`, and advances.  `norm_num` closes each
leaf.  `Spec.lean` holds the export theorem: the `OrdersAt` predicate states
every read in the exact normal form the walk produces
(`UInt32.ofNat ((ptr.toNat + (j * 5 + c) * 8) % 4294967296)`), so the loads
rewrite without address bridging.  The loop uses the `fold_sum` invariant
pattern with thirty-six existential scratch slots, and `func9_spec` transfers
the accumulator step through `wp_call_tw`.

Three lessons cost most of the day.  First, `TerminatesWith` value lists are
top-of-stack first: arguments arrive reversed relative to WASM parameter
order, results run from the last push down, and the frame stores parameters
in WASM order.  Second, a failing term-level `by` inside
`rw [if_pos (by ...)]` elaborates to `sorry`, logs an error, and lets the
rewrite take the wrong branch anyway; deciding branches at the tactic level
with `split` avoids the silent wrong turn.  Third, `wp_run` over the export's
59-local frame ground without converging on the 55-instruction loop-body
epilogue, because every step re-traverses the loop-exit continuation carried
in the postcondition.  `Epilogue.lean` cuts that tail into five segment
lemmas, each generic in the continuation and binding only the frame slots it
mentions; each walks in about two seconds where the monolithic walk did not
finish in twenty minutes.  The binder minimization is load-bearing: a segment
lemma that binds slots its frames never mention cannot be applied, because
unification has nothing to synthesize them from.

- [x] `func9_spec`: eight leaves, 179 seconds.
- [x] `epilogueA`-`epilogueE` segment lemmas.
- [x] `quote_correct`, sorry-free, standard axioms.
- [x] `tools/check-talos.sh` green for all thirteen cases.
- [x] `node test/run_all.js` green.

## 2026-07-09: the fourteenth case: `cancel` not-found, plus the scan lemma

`Project.ClobCancel.Spec.cancel_notFound` is proved, sorry-free, on the
standard axiom set: for every order array in memory and every id absent from
it, the compiled `cancel` export returns status three and the borrowed input
pointer, and the store is untouched.  The full Talos suite and the
differential suite pass.

The reusable piece is `scanFlag_spec` in `Project/ClobCancel/Scan.lean`: the
compiled id-scan loop, stated over the literal block-loop program with a
generic continuation, concluding at either exit with `List.findIdx?` as the
list-level bridge (`idIdx`).  The compiled `cancel` runs that identical scan
three times — once for the status flag, once to select the branch, once to
recompute the index — so one lemma discharges two call sites now and the
third when the found branch is proved.  The triple scan is itself a gap-list
entry: the extractor re-evaluates `findIdx?` once per use of the match
result rather than binding it once, tripling both code size and proof
obligations for this shape.

Two mechanical notes.  With a generic continuation the load trap-guards stay
as `ite`s rather than collapsing to conjunctions, and close with
`if_neg (Nat.not_lt.mpr hbound)`.  And full `simp` inside the loop-body walk
normalizes `getElem!` to `getElem?.getD` and discharges trivial invariant
conjuncts, so re-establishment tuples start at the existential and
hypothesis transfers go through `simpa`.

The found branch remains: it needs the index-recording scan variant and the
erase path, whose inline bump allocation, header stores, and two
element-copy loops follow the `append_bang` and LEB templates.

- [x] `scanFlag_spec` over the literal scan program.
- [x] `cancel_notFound`, sorry-free, standard axioms.
- [x] All fourteen check scripts and the differential suite pass.
- [ ] `cancel` found branch: index scan variant, inline allocation, copy loops.
- [ ] `postOnly`, then `limit`.

## 2026-07-13: Repository review and replacement development plan

The repository review covered the tracked source, extraction pipeline, IR interpreter, structured WASM backend, CLI, execution tests, ownership diagnostics, documentation, recent history, and the Talos proof workspace.  The untracked `leanclob/` directory is a separate nested Git repository, so the review excluded it except as background already recorded in the journal.  The old [Development Plan](plan.md) described an early compiler roadmap whose principal language, memory, WASI, comparison, and artifact-proof milestones now exist.

The replacement plan starts with two concrete compiler issues.  Source-level `LeanExe.Runtime.release` still relies on an unchecked ownership precondition, and CLOB `cancel` repeats one `findIdx?` scan three times while flattening its result.  The work order checks explicit-release ownership, evaluates matched values once, regenerates and proves complete `cancel`, then proves `postOnly`, `limit`, and `market` while extracting shared proof lemmas only from repeated cases.

The review also found documentation and tool gaps.  [Repository Overview](README.md), [Talos Proofs](proofs/talos/README.md), [Technical Summary](docs/summary.md), and [Development Agenda](docs/history/agenda.md) describe eleven artifacts, while the aggregate script now checks fourteen; CLI help omits `dump-ir` and `compile-wat` and retains a prototype-era scope sentence.  The root workspace pins Lean 4.29.1, the proof workspace pins Lean 4.31.0 and Talos commit `bb3277e21c9786e3133d5c1601e34ebdc0bea4df`, and Wasmtime defaults to 44.0.0, while `wasm-tools` and Node have no recorded versions and the Wasmtime download script does not verify archive checksums.  The plan schedules version checks and archive verification after the active semantic work.

The ordinary execution gate passed.  `node test/run_all.js` reported 114 classification cases, 8 ownership-report cases, 784 accepted cases, 34 rejections, 13 traps, 38 reference-counting cases, 70 byte-array allocation cases, 23 ASCII-string cases, 4 integer-map cases, 48 JSON cases, 35 WASI cases with 2 traps, 7 rejections, and 19 compile-only checks, 63 self-emitted LEB128 cases, 301 standard-Lean comparison cases, 58 IR-interpreter comparison cases, and 56 fuzz cases.  One leak-accounting fixture intentionally retains blocks, while the other six reported leak-free behavior.

The artifact gate also passed.  `tools/check-talos.sh` compared all fourteen regenerated WASM and WAT artifacts with their checked-in proof inputs and rebuilt the aggregate `Project` library.  The cold proof workspace first built 3,003 dependency jobs, and the final aggregate build completed 3,048 jobs; Lean reported unused `simp` arguments and variables in handwritten source and proof files, but no artifact mismatch, proof error, `sorry`, or new axiom.

Review references are [Language Specification](docs/spec.md), [User Manual](docs/manual.md), [Verifying a Program](docs/verifying.md), [Talos Proofs](proofs/talos/README.md), [Core IR](LeanExe/IR/Core.lean), [Structured WASM Instructions](LeanExe/Wasm/Instr.lean), [Compiler CLI](LeanExe/CLI.lean), and [CLOB Source](LeanExe/Examples/Clob.lean).  These repository files define the current implementation and claimed behavior.  The replacement plan keeps their roles separate and schedules a factual consistency pass.

- [x] Review the tracked repository and recent development history.
- [x] Run the complete execution suite.
- [x] Run all fourteen byte-pinned artifact checks and the aggregate proof build.
- [x] Replace the obsolete development roadmap with current priorities and exit conditions.
- [x] Check the ownership precondition for source-level release.
- [ ] Bind repeated match results once and reduce CLOB `cancel` to one identifier scan.
- [ ] Prove complete CLOB `cancel`, followed by `postOnly`, `limit`, and `market`.

## 2026-07-13: Developer guide and documentation consolidation

[Developing LeanExe](DEVELOPING.md) now defines the developer entry path.  It records the Lean 4.29.1 compiler workspace, the Lean 4.31.0 proof workspace, Wasmtime 44.0.0, the unpinned Node and `wasm-tools` gaps, system prerequisites, environment overrides, first-build commands, diagnostic commands, test gates, tracked proof artifacts, update transactions, dependency rules, and failure diagnostics.  The guide also assigns one responsibility to each maintained document so current facts do not require parallel edits in several roadmaps.

The current-state documents now agree with the aggregate proof script.  The repository overview and technical summary report fourteen artifacts, and the Talos README lists the unsigned LEB128, CLOB quote, and CLOB cancel theorems with the exact limitation that cancel covers only an absent identifier.  The technical summary no longer records volatile file sizes or test totals, `agenda.md` is an archived pointer to the development plan, the two early Talos documents identify themselves as historical experiments, and the string document identifies itself as an unimplemented proposal.

The implemented diagnostic commands now appear in every relevant interface.  CLI usage includes `dump-ir` and `compile-wat` and replaces the prototype-era scope sentence, while the repository overview, manual, specification, technical summary, and verification guide explain their roles and the proof-workspace setup.  The manual sends tool and build failures to the developer guide instead of mixing them with source rejection advice.

Documentation verification passed.  A local-link check covered all sixteen repository Markdown files, the Talos table and aggregate script each contain fourteen cases, the stale-current-state scan found no remaining eleven-artifact or prototype claims in maintained documents, and `git diff --check` reported no whitespace errors.  `lake build lean-wasm` completed 46 jobs, the no-argument CLI displayed the corrected command list with exit status 2, `dump-ir` succeeded for `LeanExe.Examples.TalosGcd.gcd`, and `node test/report_classification.js` passed all 114 cases.  The build still reports the existing unused `hsize` `simp` argument in `LeanExe/Examples/AsciiDigits.lean`; the plan keeps that warning cleanup separate from documentation work.

The execution and artifact gates recorded in the preceding review remain applicable because these edits changed documentation and CLI usage text without changing extraction, IR, ownership, ABI, or WASM emission.  The targeted CLI build and report-classification test cover the executable change.  No proof input or generated model changed.

## 2026-07-13: Development plan semantic review

A second review of `plan.md` found that its first release-ownership phase combined two different problems.  `LeanExe.Runtime.release` and the runtime counters have compiled behavior that differs from their ordinary Lean stubs, so an ownership check alone could not support the plan's source-equivalence language.  The phase also asked one change to recognize aliases through locals, structures, tags, arrays, helpers, and returns, even though the current ownership summaries support a narrower direct-handoff judgment.

The revised phase now defines the runtime-intrinsic semantic boundary before implementation and treats release as consumption of one owned root reference rather than graph-wide uniqueness.  Its first accepted subset is a direct fresh local or fresh helper result at final use, plus a statically known owner-zero array release; branch-dependent ownership, container escapes, loop-carried fields, and unresolved aliases reject until a later focused increment proves them.  The plan removes the proposed test-only bypass, requires an inventory of every existing explicit release, and separates ordinary Lean comparison claims from claims under LeanExe's runtime extension.

The matched-value phase now requires reduced tests for unused trapping payloads and heap-bearing results in addition to the CLOB scan count.  The CLOB proof phase defines `UInt64` source equivalence separately from natural-number conservation with no-overflow bounds, states shared layout and ownership preconditions, proves `findBest` before `postOnly`, and proves `matchFuel` before `limit` and `market`.  `depth` now appears in both the proof scope and the completion criteria.

The baseline now records the completed documentation work and the remaining tool gaps.  CLI errors, Node and `wasm-tools` versions, Wasmtime hashes, cold-build reporting, and known warnings form a numbered phase required by the next stable point.  The general lowering theorem moved to later work because the completion criteria do not require it, and the proof-consolidation phase now runs during CLOB proofs once repetition establishes a common statement.

The documentation baseline was committed as `5659ef5` before this plan revision.  The plan link resolves, its prose passes the repository style scan, and `git diff --check` reports no whitespace errors.  No compiler, artifact, proof, or generated model changed in this revision.

## 2026-07-13: Runtime intrinsic semantics and release audit

The runtime intrinsic boundary now has one explicit semantic statement.  Ordinary Lean and the reference IR interpreter evaluate the four counters and `LeanExe.Runtime.release` as zero-valued stubs, while generated WASM maintains allocator counters and consumes one owned root reference.  A nonzero release validates the root, increments the release counter, decrements its reference count, recursively decrements marked children when the count reaches zero, increments the free counter, and returns the resulting free count; owner `0` changes no state.

The source judgment concerns the released root reference rather than graph-wide uniqueness.  Release requires final use of a direct fresh local or fresh helper result, without a copied alias, return, container escape, or repeated release; a statically owner-zero array also qualifies as a no-op.  A child shared through a retained reference may remain live, while branch-selected roots, conditionally owned arrays, structure fields, loop-carried roots, consuming parameters, and unresolved aliases require analysis beyond the initial judgment.

The tracked example source contains twenty-two explicit release calls.  Eleven consume direct fresh roots, four consume fresh helper results, one consumes a branch-selected fresh root, two consume conditionally owned array-operation results, one releases a statically owner-zero out-of-bounds update, one consumes a function parameter, and two consume roots carried in structures.  The table records the source classification that the compiler checker and focused tests must reproduce.

| Source release sites | Count | Audit result |
|----------------------|-------|--------------|
| `Correctness`: inline replicate, three nested or structured arrays, `unusedRecursiveRuntimeReleaseFrees`, `sharedRecursiveChildReleaseStats`, and three public-layout arrays; `ByteArrayPrograms`: `boxFreeStats` and `chainFreeStats` | 11 | Direct fresh root with no root use after release.  The shared-child case remains valid because construction retains the second child reference. |
| `Correctness.recursiveScenarioHelperRuntimeReleaseStats`, `ByteArrayPrograms.sharedPairFreeStats`, and both roots in `JsonMergeTreeCommand.makeMergedTreeValue` | 4 | Helper result whose fresh root must appear in the helper ownership summary. |
| `Correctness.recursiveScenarioRuntimeReleaseStats` | 1 | Fresh on every branch, but provenance is branch-dependent and lies outside the initial checker. |
| `Correctness.borrowedArrayPopEmptyReleaseFrees` and `borrowedArrayReverseSingletonReleaseFrees` | 2 | The result may borrow or own according to the input and operation path, so the initial checker must reject it. |
| `Correctness.borrowedArraySetOobReleaseFrees` | 1 | The index equals the source size, making the update a statically borrowed owner-zero no-op. |
| `JsonTreeCommand.insertOwned` | 1 | Consumes a function parameter after building a replacement and requires a consuming-parameter judgment. |
| `JsonGcTreeRewrite.runRoundsFuel` and `runConfig` | 2 | Consume a loop-carried structure field and a helper-result field, which require field-sensitive ownership analysis. |

The specification, manual, repository overview, and developer guide now state the same boundary.  The first compiler increment will accept only the direct cases and owner-zero case, reject unsupported provenance with the declaration and released expression, and expose the judgment in the ownership report.  Existing command examples that rely on consuming parameters or structure fields need a later proved increment or a source revision that exposes a direct handoff.

- [x] Define generated runtime counter and release transitions.
- [x] Separate ordinary Lean and IR-interpreter behavior from generated WASM behavior.
- [x] Define the initial direct-handoff judgment.
- [x] Classify all twenty-two tracked source release sites.
- [x] Enforce the judgment before IR extraction and report its result.

## 2026-07-13: Direct release handoff checker

`LeanExe/Extract/ReleaseCheck.lean` now validates every explicit source release after the first extraction pass computes helper fresh-result summaries and before the accepted IR reaches WASM emission.  It accepts recursive constructors, array literals and replication, helper results whose owner offset is fresh, and the exact owner-zero `setIfInBounds values.size` form.  Each accepted judgment records its declaration, source binding, and provenance for `ownership-report`.

The checker rejects later use, repeated release, direct aliases, container escape, return escape, parameter ownership, branch-selected roots, conditionally owned array operations, structure fields, loop-carried roots, and helper results without a fresh-owner summary.  Diagnostics name the declaration and released expression, then state the known provenance and rejection reason.  Eight reduced source fixtures cover use after release, double release, aliasing, container escape, return escape, parameter consumption, an interprocedural alias, and an out-of-bounds update over a possibly owned helper parameter; the existing branch, pop, and reverse fixtures cover unresolved conditional provenance.

The audit required one source correction and two explicit deferrals.  `JsonTreeCommand.insertOwned` no longer contains a redundant source release because its `Array.foldl` caller already uses the compiler's proved accumulator-replacement release rule, preserving the tree WASI pipeline.  `JsonMergeTreeCommand.makeMergedTree` now rejects when a source root has entered the heap-valued merged binding, and `JsonGcTreeRewrite.transform` rejects when `runRoundsFuel` releases the `tree` field of loop-carried state; both sources remain requirements for later retained-handoff and field-sensitive analysis.

Focused verification passed 781 accepted core cases, 45 exact rejections, 13 traps, 10 ownership-report cases, and 38 reference-counting cases.  The reference-counting suite retains Wasmtime checks for direct fresh arrays, recursive roots, fresh helper results, shared retained children, and an owner-zero array release.  The WASI suite passed 33 program cases, two traps, nine rejections, and sixteen compiles after the merge assertion was corrected to check its heap-bearing escape reason.

- [x] Validate every reachable explicit release before final extraction.
- [x] Report accepted source judgments through `ownership-report`.
- [x] Add exact rejection fixtures for every initial unsupported shape.
- [x] Preserve the JSON tree pipeline through compiler-managed fold cleanup.
- [x] Run the complete execution, WAT, and Talos gates.

The complete execution gate passed 114 report-classification cases, 10 ownership-report cases, 781 accepted core cases, 45 rejections, 13 traps, 7 leak-accounting cases, 38 reference-counting cases, 70 byte-array allocation cases, 23 ASCII-string cases, 4 integer-map cases, 48 JSON cases, 33 WASI program cases with 2 traps, 9 rejections, and 16 compiles, 63 self-emitted LEB128 cases, 301 standard-Lean comparisons, 58 IR comparisons, and 56 fuzz cases.  The WAT gate passed nine entries after replacing the deferred `JsonGcTreeRewrite.transform` matrix entry with the accepted `JsonTypedDecode.transform`; every parsed WAT artifact matched the directly emitted binary byte-for-byte.  The Talos gate compared all fourteen regenerated WASM and WAT artifacts with their checked-in proof inputs and rebuilt the aggregate `Project` library without an artifact mismatch or proof error.

## 2026-07-13: Single-evaluation array search matches

`Array.findIdx?`, `Array.find?`, and `ByteArray.findIdx?` now bind one encoded search result whose zero value means missing and whose positive value is the found index plus one.  Extraction derives the public `Option` tag and payload from that local, and structured match results use a statement-level branch before result slots are assigned.  CLOB `cancel` therefore scans the order array once and reuses the recorded index in `eraseIdx!`.

The reduced fixtures cover a scalar helper result, unused structure fields that contain trapping array reads, structure results, fresh array results, and an executed trapping predicate.  The heap fixture allocates the literal search array and one branch result, releases the returned root once, and records `2 0 1 1` for allocation, retain, release, and free counts on both found and missing inputs.  Standard Lean and Wasmtime agree on both scalar branches and both heap-result branches, while the scalar cases also agree with the IR interpreter.

The CLOB WAT shrank from 23,020 bytes to 19,838 bytes in the reviewed text rendering.  The diff removes two full predicate scans, introduces one encoded-index local, and preserves the erase allocation, header stores, and two copy loops with local renumbering.  The checked Talos artifact remains unchanged, so `tools/check-talos-clob-cancel.sh` reports the expected byte mismatch until the complete cancel proof in the next phase accepts the regenerated artifact.

Checks run:

- [x] `lake build lean-wasm LeanExe.Examples.Correctness` completed successfully.
- [x] `node test/matched_values.js` returned `checked 4 matched-value IR cases and 1 WAT scan case`.
- [x] `node test/core_correctness.js` returned `checked 791 accepted, 45 rejected, and 14 trapped cases`.
- [x] `node test/refcount.js` returned `checked 40 refcount cases` with both matched-array branches at `2 0 1 1`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 309 standard Lean comparison cases` and `checked 62 IR interpreter comparison cases`.
- [x] Review of `/tmp/clob-cancel-before.wat` and `/tmp/clob-cancel-after.wat` accounted for every removed scan and retained found-branch block.
- [x] `tools/check-talos-clob-cancel.sh` stopped at the expected proof-input byte comparison before rebuilding the stale proof.

## 2026-07-13: Single-scan cancel proof checkpoint

The CLOB scan lemma now follows the single generated loop and records an encoded first-match index.  Its absent case returns zero after reaching the array length, while its found case returns `UInt64.ofNat i + 1` with the matched order fields still loaded.  The list bridge continues to identify the first matching source index through `List.findIdx?`.

The existing `cancel_notFound` theorem retains its quantified order list, absent-identifier premise, borrowed input pointer, status-three result, and exact store equality.  Its proof now invokes the scan lemma once and follows the generated not-found helper call directly.  The transactional artifact update replaced the WASM, WAT, and generated Talos model only after the theorem rebuilt successfully.

Checks run:

- [x] `lake build Project.ClobCancel.Spec` completed 3,009 proof jobs.
- [x] `tools/check-talos-clob-cancel.sh --update` regenerated the three proof inputs and rebuilt `Project.ClobCancel.Spec`.
- [x] The checked WASM size changed from 2,216 bytes to 1,930 bytes after removal of the duplicate scans.

## 2026-07-13: Complete single-scan cancel theorem

`Project.ClobCancel.Spec.cancel_found` proves the allocating branch for every
represented order array whose input and fresh result occupy disjoint,
nonwrapping memory regions.  The proof follows the inline bump allocator,
checks all six header stores, writes the output length, and proves both word
copy loops with decreasing measures.  The final list argument converts the
copied prefix and suffix into `OrdersAt st' (g0 + 48) (os.eraseIdx i)`.

`Project.ClobCancel.Spec.cancel_correct` selects the missing or found theorem
from the single `idIdx` result.  Its missing branch returns the borrowed input
pointer and exact unchanged store without allocator assumptions.  Its found
branch returns a refcount-one array, advances the heap top by the exact object
size, increments the allocation counter once, preserves all other globals and
pages, and leaves every byte below the old heap top unchanged.

The focused proof build completed 3,009 jobs without a warning.  A repository
scan found no `sorry`, admitted theorem, new axiom, or diagnostic trace in the
CLOB cancel proof directory.  The cancel artifact check compared regenerated
WASM and WAT with the checked proof inputs and rebuilt the theorem; the later
aggregate Talos and complete execution gates also passed.

- [x] Prove the inline allocator and six header stores.
- [x] Prove the prefix and suffix copy loops.
- [x] Prove exact `eraseIdx` contents and output ownership.
- [x] Combine the found and missing branches in `cancel_correct`.
- [x] Run `tools/check-talos-clob-cancel.sh`.
- [x] Run the aggregate proof and complete execution gates.

## 2026-07-13: Quote artifact repair and phase gates

The statement-level branch materialization introduced for matched structure values also changed the CLOB quote artifact.  Its six `quoteStep` result fields now receive values inside one selected statement branch instead of projecting six independently guarded expressions.  The first aggregate artifact check found this omitted Phase 2 consequence, and the transactional `--update` command restored the checked inputs when the existing proof did not accept the regenerated program.

The repaired `Project.ClobQuote.Step.func9_spec` follows the selected statement branch and retains the same source-level result.  The focused quote proof and specification build pass, and `tools/check-talos-clob-quote.sh` compares the regenerated WASM and WAT with the checked inputs before rebuilding them.  The WASM artifact decreased from 2,853 bytes to 2,047 bytes because the generated function no longer repeats the branch condition for each field.

The aggregate `tools/check-talos.sh` gate compared all fourteen artifacts and completed 3,048 build jobs without an artifact mismatch or proof error.  The build reports existing linter warnings in older handwritten proofs, which remain Phase 6 work.  `node test/run_all.js` passed 114 report-classification cases, 10 ownership-report cases, the JavaScript execution guard, 791 accepted cases, 45 rejections, 14 traps, four matched-value IR cases, one WAT scan, seven leak-accounting cases, 40 reference-counting cases, 70 byte-array allocation cases, 23 ASCII-string cases, four integer-map cases, 48 JSON cases, 33 WASI program cases, 63 self-emitted LEB128 cases, 309 standard-Lean comparisons, 62 IR comparisons, and 56 final cases.

## 2026-07-14: CLOB `findBest` branch gate

The Phase 4 test review found that `LeanExe/Examples/ClobTest.lean` was absent from the complete test runner and that the standard-comparison matrix contained no CLOB entries.  Earlier journal text claimed six `scenario` comparisons and one `cancel` comparison, but the tracked matrix no longer contained those cases.  The source guards therefore ran only when a developer named their module directly, and the full gate did not provide the claimed differential coverage.

The runner now builds `LeanExe.Examples.ClobTest`, whose direct `findBest` guards cover empty input, a same-side maker, a same-trader maker, a maker outside the limit price, an eligible maker after a rejected prefix, better and worse candidates, equal-price FIFO ties, and both taker sides.  Five public-ABI comparisons pass arrays of five-word `Order` structures and a scalar `Order` argument to the exported function, then compare its `Option Nat` result with ordinary Lean.  The comparison code reuses the existing ABI layout functions and adds no source wrapper or third-party dependency.

`lake build LeanExe.Examples.ClobTest` completed three jobs with all guards accepted.  The focused public-ABI command matched the buy-side replacement case, and the complete standard-comparison matrix passed 314 standard-Lean cases and 62 IR cases.  The five added cases explain the standard total's increase from 309 to 314; the IR total is unchanged because its interpreter does not accept heap-backed public ABI arguments.

## 2026-07-14: Shared CLOB order-array model

The `findBest` artifact confirmed that quote, cancel, and the remaining CLOB proofs consume the same five-word order-array representation.  `Project.Clob` now owns `OrderL` and `OrdersAt`, while quote retains its fold model and cancel retains its identifier scan and allocation arithmetic.  This completes the first Phase 5 reuse item after three independent artifacts established the shared statement.

The move changes no definition body or theorem statement after namespace resolution.  `lake build Project.ClobQuote.Spec Project.ClobCancel.Spec` rebuilt the shared module, quote step and specification, cancel scan, and complete cancel specification in 3,010 jobs.  Both proofs remain accepted without editing their generated `Program.lean` files or checked WASM and WAT inputs.

## 2026-07-14: CLOB `findBest` proof scaffold

The `clob_find_best` Talos case now pins the compiled `LeanExe.Examples.Clob.findBest` export.  The artifact is 3,462 bytes of WASM and 42,412 bytes of printed WAT, with the public wrapper at function 8, the fuel loop at function 7, scalar decision helpers at functions 1, 4, 5, and 6, and runtime functions at indices 9 through 12.  The runtime definitions match the shared allocator, reset, retain, and index-parametrized release definitions by reduction.

`Project.ClobFindBest.Model` restates opposite-side selection, crossing, eligibility, better-price comparison, fuel recursion, and the public two-word `Option Nat` result.  `Project.ClobFindBest.Helpers` proves the four scalar helpers over arbitrary orders and stores, including the short-circuit path that skips the crossing call when side or trader eligibility fails.  The helper build completed 3,006 jobs without a warning after unused simplification arguments were removed.

`tools/check-talos-clob-find-best.sh --update` generated the WASM, WAT, and decoded model transactionally and built the temporary specification module.  The case belongs to the aggregate artifact script and proof-library import, but this checkpoint does not count it as a verified artifact because the fuel-loop and export theorems remain.  The next increment proves the exact `findBestL` result for every represented order array before updating the theorem inventory.

The checked artifact comparison passed after generation.  `lake build Project.Runtime.Checks Project` then completed 3,053 jobs, including the new runtime pins and aggregate proof-library import.  The build reported only warnings that predate this proof directory.

## 2026-07-14: Complete CLOB `findBest` proof

`Project.ClobFindBest.Loop.func7_spec` proves termination and the exact `findBestL` result for every represented order array, taker, and input length below `2^32`.  Its postcondition covers all five generated result branches and preserves the complete store.  `Project.ClobFindBest.Spec.findBest_correct` connects the public six-argument ABI to the source two-word `Option Nat` result with the same store guarantee.

`Project.ClobFindBest.Spec.findBestL_best` proves the source search's economic property for a valid taker side.  A successful result is in bounds and eligible, no eligible candidate has a better price, and an equal-price eligible candidate cannot precede the returned index.  The proof derives the result from a prefix invariant shared with the exact fuel-recursive model.

The checked artifact remains 3,462 bytes of WASM and 42,412 bytes of WAT.  The generated loop calls function 5 at four syntactic sites and performs the price comparison inline; function 6 remains present in the compiled module but function 7 does not call it.  The proof follows those emitted instructions, leaves `Program.lean` unchanged, and adds no axiom, admission, or third-party dependency.

- [x] `lake build Project.ClobFindBest.Spec` completed 3,008 jobs without a warning in the `findBest` modules.
- [x] `tools/check-talos-clob-find-best.sh` matched the checked WASM and WAT and rebuilt the specification.
- [x] The focused artifact check reported only the pre-existing `AsciiDigits.lean` unused-argument warning scheduled for Phase 6.

## 2026-07-14: CLOB `postOnly` branch gate

The existing source guards covered duplicate identifiers, invalid sides, zero quantities, crossing orders, and successful appends, but omitted zero identifiers and zero traders.  They inspected status and selected book lengths rather than the complete `OpResult`.  The standard/WASM comparison matrix contained no `postOnly` case.

The branch gate now checks all five `validOrder` failure paths, the `findBest` crossing result, and the successful append result.  Each comparison passes an order array and taker through the public ABI, then compares status, every returned order field, and the empty trade array with ordinary Lean.  The result layout and serializers use the existing structured ABI test framework and add no source wrapper or dependency.

`lake build LeanExe.Examples.ClobTest` accepted every source guard, including the two new validity cases.  `node tools/compare-standard.js --self-test` passed 321 standard-Lean cases and 62 IR cases, with all seven `postOnly` comparisons succeeding.  The standard total increased from 314 to 321, while the IR total remains unchanged because the interpreter does not accept heap-backed public ABI arguments.

## 2026-07-14: CLOB `postOnly` proof scaffold

The `clob_post_only` case now pins the compiled `LeanExe.Examples.Clob.postOnly` export.  The artifact is 5,915 bytes of WASM and 70,775 bytes of WAT, with the public wrapper at function 17 and runtime functions at indices 18 through 21.  The runtime functions match the shared allocator, reset, retain, and index-parametrized release definitions by reduction.

`Project.ClobPostOnly.Model` states the five validity conditions and the invalid, would-cross, and appended source outcomes over the shared order representation.  Invalid and would-cross results borrow the input book and allocate one empty trade array.  The successful result allocates both the appended book and an empty trade array, so its artifact theorem requires a separate two-allocation postcondition.

`tools/check-talos-clob-post-only.sh --update` generated the proof inputs and decoded model transactionally, then built the placeholder specification.  `lake build Project.Runtime.Checks Project` completed 3,057 jobs with the new runtime pins and aggregate import.  The build reported existing linter warnings outside the new proof directory, and the case does not enter the verified theorem count until its input-generic specification is complete.

## 2026-07-14: CLOB `postOnly` helper proofs

`Project.ClobPostOnly.SearchHelpers` proves side selection, crossing, eligibility, and better-price behavior at the new artifact's function indices.  The instruction bodies match the earlier `findBest` helpers apart from their indices and internal call targets.  Each theorem ranges over arbitrary scalar orders and preserves the store.

`Project.ClobPostOnly.ValidOrder.func5_spec` proves that the generated identifier scan returns one exactly when an order with the requested identifier occurs.  Its loop invariant records a clean processed prefix, reads all five fields through the shared `OrdersAt` predicate, and terminates by decreasing the unprocessed length.  `func6_spec` combines that result with nonzero identifier, nonzero trader, valid side, and nonzero quantity in the emitted short-circuit order.

`lake build Project.ClobPostOnly.SearchHelpers` completed 3,006 jobs, and `lake build Project.ClobPostOnly.ValidOrder` completed 3,008 jobs.  Both focused targets build without a warning in the new proof files.  The proofs add no source wrapper, generated-file edit, axiom, or admission.

## 2026-07-14: CLOB `postOnly` search proof

`Project.ClobPostOnly.FindBest.func12_spec` proves termination and the exact source `findBestL` result for every represented order array and taker.  It instantiates the established prefix invariant at function 12 and calls the new artifact's eligibility helper at function 10.  All five generated result branches preserve the complete store.

`Project.ClobPostOnly.FindBestWrapper.func13_spec` reads the array length, checks the fuel addition for overflow, and invokes function 12 with an empty initial result.  It returns the same two-word option ABI as the standalone `findBest` export and preserves the store.  The separate wrapper file keeps later wrapper edits from forcing another elaboration of the 1,005-line loop proof.

`lake build Project.ClobPostOnly.FindBest` completed 3,007 jobs in 218 seconds.  The wrapper target then completed 3,008 jobs in five seconds.  Both builds produced no warning, and the adaptation leaves the generated `Program.lean` unchanged.

## 2026-07-14: Shared fixed-array allocation predicate

`Project.Clob` now defines the byte count and six-word allocation header for a fixed-width array.  The predicate records the runtime magic word, reference count, byte capacity, array kind, element stride, and owner mask at their exact offsets from the returned data pointer.  Order and trade arrays can specialize one statement instead of defining separate header layouts.

The complete `cancel` theorem now defines `FreshOrderArrayAt` as the stride-five specialization of the shared predicate.  Its byte-count definitions remain local because its arithmetic proof depends on their direct normal form, while later artifacts can use the generic count from the start.  The theorem statement and generated artifact remain unchanged.

`lake env lean Project/ClobCancel/Spec.lean` rebuilt the complete found and missing proof after rebuilding `Project.Clob`.  The target passed without an error or warning.  This checkpoint adds no axiom, admission, dependency, or generated-file edit.

## 2026-07-14: Shared CLOB memory frame theorem

`Project.Clob.OrdersAt.frame` preserves a represented order array across writes above a stated heap boundary.  Its hypotheses require an unwrapped 32-bit input extent, the input below the boundary, unchanged page count, and byte equality below that boundary.  The proof derives every header and field read with the common `read64_congr` lemma and preserves each memory bound through page equality.

The invalid and crossing `postOnly` branches can now state both the borrowed input pointer and its exact source contents after allocating the trade array.  Later matching proofs can apply the same theorem when fresh result arrays occupy memory above their input books.  This removes five-field readback proofs from each allocation branch.

`lake env lean Project/Clob.lean` checked the new theorem without an error or warning.  The theorem uses the existing memory model and adds no axiom or dependency.  No artifact input changed.

## 2026-07-14: CLOB `postOnly` allocation vocabulary

`Project.ClobPostOnly.Allocation` specializes the shared fixed-array definitions for stride-five orders and stride-four trades.  `FreshTradeArrayAt` combines the common owned-array header with the emitted zero length at the returned data pointer.  The order byte count uses the generic fixed-width calculation from the start.

The module also proves the exact results of functions 14, 15, and 16.  These helpers return would-cross status two, success status zero, and invalid status one while preserving the store.  The public wrapper proof can consume their behavior through the call rule.

`lake build Project.ClobPostOnly.Allocation` completed 3,005 jobs without an error or warning.  The generated program remains unchanged.  The module adds no axiom, admission, or dependency.

## 2026-07-14: CLOB `postOnly` invalid branch

`Project.ClobPostOnly.Invalid.postOnly_invalid` proves the public function-17 path for every represented book and every order that fails `validOrderL`.  The export returns status one, the borrowed input-book pointer, and a fresh empty trade array at the old heap top plus 48 bytes.  The theorem re-establishes the exact input-book contents through `OrdersAt.frame` after the allocation writes.

The proof follows the emitted free-list loop, bump allocation, page check, six header stores, zero-length store, and allocation-counter update.  Its empty-free-list and fit hypotheses select the no-growth bump path.  The postcondition records the stride-four header, reference count one, eight-byte capacity, zero length, unchanged page count, advanced heap top and allocation count, and byte equality below the old heap top.

`lake env lean Project/ClobPostOnly/Invalid.lean` checked the theorem without an error or warning.  A targeted Lake build produced the module object after rebuilding invalidated shared dependencies.  The proof contains no axiom, admission, generated-file edit, or additional dependency.

## 2026-07-14: CLOB `postOnly` crossing branch

`Project.ClobPostOnly.Crossing.postOnly_crossing` proves function 17 for every valid order whose source `findBestL` result is `some maker`.  The proof composes the exact validity and search theorems at functions 6 and 13, then selects the generated would-cross branch.  The public result contains status two, the borrowed input book, and one owned empty trade array.

The allocator postcondition matches the invalid branch: heap top advances by 56 bytes, allocation count advances once, and page count remains fixed.  The fresh array has reference count one, eight-byte capacity, array kind two, stride four, owner mask zero, and length zero.  `OrdersAt.frame` proves that the seven allocation writes preserve the represented input book.

Rebuilding the shared `FindBest` theorem after the CLOB model edit completed 3,007 jobs in 325 seconds.  `lake build Project.ClobPostOnly.Crossing` then completed 3,012 jobs in 24 seconds without an error or warning.  The crossing theorem adds no axiom, admission, dependency, or generated-file edit.

## 2026-07-15: Compiler Workspace Upgrade to Lean 4.31

The root `lean-toolchain` now pins Lean 4.31.0, matching the Talos proof workspace.  Compatibility edits use Lean 4.31's direct `Nat` comparisons, proof-bearing `ByteArray.get`, nested error contexts, and generated recursion declarations.  The upgrade adds no dependency and leaves the public compiler commands unchanged.

Lean 4.31 places equation-compiled natural-number recursion in a generated `<declaration>._f` helper, and structural `brecOn` helpers can apply `_f` to captured arguments before the recursive argument.  Extraction now recognizes that shape, instantiates and beta-reduces the helper, and traverses the helper dependencies when building the accepted declaration set.  The release checker validates releases inside `_f` under the source declaration name, which restores rejection of a loop-carried structure-field release in `JsonGcTreeRewrite.runRoundsFuel`.

Repository instructions now require one resource-limited user scope around every Lean, Lake, compiler, or compiler-spawning command.  The scope sets `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=1G`, `CPUQuota=100%`, `nice -n 10`, `ionice -c 3`, and a command-specific timeout.  Lake 5.0.0 exposes no job-count option, so the CPU quota limits Lake and all child processes to one core and concurrent Lean processes remain prohibited.

The complete root gate passed after a clean build.  It reported 114 classification cases, 10 ownership-report cases, 791 accepted cases, 45 rejections, 14 traps, 4 matched-value IR cases, 1 matched-value WAT assertion, 7 leak-accounting cases, 40 reference-counting cases, 70 byte-array allocation cases, 23 ASCII-string cases, 4 integer-map cases, 48 JSON cases, 33 WASI program cases with 2 traps, 9 rejections, and 16 compiles, 63 self-emitted LEB128 cases, 321 standard-Lean comparisons, 62 IR comparisons, and 56 fuzz cases.  The clean build exposed five modules that the complete runner consumed without building explicitly, so `test/run_all.js` now names them in its initial Lake build.  Removing the obsolete `hsize` simplification argument also leaves the root build free of warnings.

The WAT round-trip gate passed all nine entries.  Compiler-only comparison against the sixteen checked Talos inputs matched fifteen WASM and WAT pairs; `assoc_list` differs because the Lean 4.31 form removes eight WAT lines that normalize an already Boolean result before comparing it with one.  Disk cleanup removed the proof cache, and the in-progress `postOnly` proof has uncommitted work, so this migration neither updated proof inputs nor ran the proof build; `assoc_list` regeneration and proof validation remain required before the toolchain artifact gate passes.

- [x] Pin the root compiler workspace to Lean 4.31.0.
- [x] Support Lean 4.31 recursion helpers and release validation.
- [x] Constrain every Lean process by memory, CPU, I/O priority, and timeout.
- [x] Run the complete root execution and WAT gates.
- [x] Regenerate and prove the changed `assoc_list` artifact after proof work resumes.

## 2026-07-15: CLI Failure Interface

`LeanExe.CLI` now classifies handled failures at explicit operation boundaries.  Command-use and bound errors return status two, source and project-input rejections return three, I/O failures return four, and encoder invariants or exceptions outside those boundaries return five.  Each stderr record names the category and command, includes available module, entry, and output-path context, and retains the detailed extractor or operating-system message.

`test/cli_errors.js` runs the executable as a child process and checks malformed command shape, nonnumeric and excessive bounds, a missing module, a missing entry, a wrong WASI entry type, an unsupported declaration, a reserved export name, a failed output write, and help output.  The test also requires empty stdout on failure, the documented status, contextual stderr, no ANSI escape, and no `uncaught exception` prefix.  The complete constrained root gate passed 114 classification cases, 10 ownership-report cases, 9 CLI failure cases, 791 accepted cases, 45 rejections, 14 traps, 40 reference-counting cases, 321 standard-Lean comparisons, 62 IR comparisons, and 56 fuzz cases; the nine-entry WAT round-trip also passed.

This work leaves the Talos proof workspace unchanged.  Existing proof support already includes `read_frames`, `OrdersAt`, `OrdersAt.frame`, and `FreshFixedArrayAt`, which cover repeated read-over-write, represented-order, framing, and fixed-array-header obligations.  When proof work resumes, the next reuse review should compare the completed cancel copy loops with the in-progress `postOnly` append branch and add a shared theorem only if both need the same combined allocation, content, and frame postcondition; a new tactic should require repeated address or invariant forms that the current `read_frames` tactic does not solve.

- [x] Define one public CLI failure status scheme.
- [x] Add process-level tests for every required failure path.
- [x] Preserve successful compiler output and WAT round trips.
- [ ] Review cancel and `postOnly` copy obligations together when Talos proof work resumes.

## 2026-07-15: Node and `wasm-tools` Pins

The repository now pins Node 24.13.0 in `.node-version` and `wasm-tools` 1.251.0 in `.wasm-tools-version`.  Node generates test runners and compares process output, while `wasm-tools` prints the WAT that Talos decodes, so the gates reject an unreviewed version change.  The pins add no package manager, library, or downloaded dependency.

`tools/check-node-version.js` compares `process.version` with the Node pin before `test/run_all.js` starts a build, and the runner uses that process's `execPath` for every Node child test.  `tools/check-wasm-tools-version.sh` validates the executable selected through `WASM_TOOLS`, `PATH`, or `$HOME/.cargo/bin`, and both `tools/check-wat.sh` and `tools/check-talos-case.sh` invoke it before generating an artifact.  A mismatch names the expected version, first observed version line, and selected executable without ANSI output.

The Node syntax, pin, and `execPath` checks passed with `v24.13.0`, and the `wasm-tools` success and deliberate mismatch paths returned the expected statuses and messages.  The version-enforced WAT gate checked `wasm-tools 1.251.0`, rebuilt `lean-wasm` under the repository resource limits, and matched all nine binary and text entries.  No Talos proof command ran, and no checked proof input changed.

- [x] Record and enforce Node 24.13.0.
- [x] Record and enforce `wasm-tools` 1.251.0.
- [x] Run the version-enforced WAT gate.

## 2026-07-15: Wasmtime Archive Verification

The [official immutable Wasmtime 44.0.0 release](https://github.com/bytecodealliance/wasmtime/releases/tag/v44.0.0) publishes SHA-256 digests for every release asset.  `tools/download-wasmtime.sh` now records the CLI and C API archive digests for `aarch64-linux` and `x86_64-linux`.  A version or platform without built-in digests requires explicit `WASMTIME_CLI_SHA256` and `WASMTIME_C_API_SHA256` values before the script creates its destination directory or contacts a release server.

The downloader verifies a cached archive before reuse and verifies a new `.part` file before replacing the cache or extracting it.  A corrupt cached file triggers a replacement download, while a corrupt downloaded file produces a nonzero failure and never reaches extraction.  The script requires `sha256sum`, preserves its two stdout environment assignments, and sends recovery and failure details to stderr.

The cached aarch64 CLI and C API archives matched the official digests `294cae921fb88cbbcb60a914eaaaf313df3249d718609afb5804186b3f1912f5` and `6f1fb604f6d3f307f2d093bdc18e9781c85692e17c2360f5975875817adc34ab`.  The official x86-64 CLI and C API digests are `52eba06fe9f4364aa6164a4a3eafb2ca692ba9a756cbe8137b5574871f8cbfc8` and `e193aa35338637d84f172323a909cebb907c14c55b5a4b5bdbf89f5cd0b89c81`.  An isolated `file://` fixture confirmed wrong-cache detection, verified replacement, extraction, and symlink creation without modifying the repository cache.

- [x] Record all four official Wasmtime 44.0.0 Linux archive hashes.
- [x] Verify cached and downloaded archives before extraction.
- [x] Reject unchecked version and platform overrides.
- [x] Test corrupt-cache replacement in an isolated local fixture.

## 2026-07-15: Separate Talos Setup and Gate Output

The aggregate Talos driver now checks all sixteen WASM and WAT pairs before it consults the proof workspace.  Each case runs in a new `--artifacts-only` mode that suppresses successful root Lake output and prints one matched-case record.  The first byte mismatch therefore stops the gate before dependency builds or proof warnings can obscure its case name and file paths.

The default aggregate then runs `lake --no-build` for `Project`, with informational and warning output suppressed.  A missing or stale target produces a short Lake error list and an instruction to run `tools/setup-talos.sh`.  That setup command owns the potentially large dependency and proof build, while ordinary per-case checks retain their focused proof build and transactional `--update` behavior.

Bash syntax checks, argument-conflict checks, and `git diff --check` passed.  The constrained aggregate artifact test matched `gcd` and stopped at the known Lean 4.31 `assoc_list` WASM difference at byte 222.  A constrained no-build probe reported four stale proof targets in 1.3 seconds without compiling them; no hard Talos proof ran, and the current `postOnly` work remained unchanged.

- [x] Add artifact-only per-case checks.
- [x] Compare every aggregate artifact before proof output.
- [x] Give cold and stale proof builds a separate command.
- [x] Preserve per-case update rollback and proof validation.

## 2026-07-15: Lean 4.31 `assoc_list` Artifact

The refreshed `assoc_list` artifact removes one eight-instruction Boolean normalization after the identifier comparison.  The deleted sequence compared an existing zero-or-one result with zero, inverted that comparison, rebuilt zero or one through a conditional, and then compared the rebuilt value with one.  Lean 4.31 leaves the original zero-or-one result in place for the final comparison.

The WASM file shrank from 3,552 to 3,539 bytes, and the WAT and generated Talos model each lost the corresponding eight instructions.  The handwritten `Project.AssocList.Spec` file required no edit and rebuilt successfully after transactional regeneration.  The refreshed WASM, WAT, and model SHA-256 hashes are `6b356640062b5977acaf5459a6d3f8c3f1184c1a3e442b963c54e7a1d3a5a1de`, `231aa47360d41c24019b4447391a2d3d72f3c9ee11d6cc450238cf0e41ad48cd`, and `b5375bb25bec502a9d3291df2fea8f2b691f510df3f914e08582fedd581637a0`.

The constrained per-case update completed 3,006 Lake jobs in 18 seconds.  The constrained aggregate artifact-only gate then matched all sixteen WASM and WAT pairs in eight seconds.  Both commands ran with the repository memory, CPU, priority, and timeout limits, and neither command changed the in-progress `postOnly` proof files.

- [x] Review the emitted instruction difference.
- [x] Regenerate the checked WASM, WAT, and Talos model.
- [x] Rebuild the existing input-generic theorem.
- [x] Match all sixteen artifacts against Lean 4.31 output.

## 2026-07-15: Proof Maintenance and Fixed-Array Framing

Stored Lean traces contained 267 warning records across twelve handwritten proof modules, including duplicate records for unreachable tactics.  Focused edits removed the warning in `FoldSum.Spec`, four interface-binder warnings in `LebU32.Copy`, and all seventeen warnings in `Runtime.Tree` and `Runtime.TreeSpec`.  Constrained `--wfail` builds completed in 3.2 seconds for `Runtime.Tree`, 13 seconds for `Runtime.TreeSpec`, and 2.8 seconds for `LebU32.Copy` after a separate three-second dependency rebuild, without a warning in any checked target.

One Lake invocation named `Validate`, `FoldSum`, and `SharedPair` as separate targets.  Lake started two Lean children concurrently even though their common cgroup limited the process tree to one CPU and six gigabytes, which violated the repository rule against concurrent Lean processes.  I interrupted that build, restored the unverified `Validate` and `SharedPair` edits, confirmed their diffs were empty, and used exactly one target in every later Lake invocation.

An isolated `SharedPair.Spec` warning-only build reached its 30-minute timeout, and an isolated `LebU32.Iter` warning-only build reached its 15-minute timeout.  Host process checks showed one Lean child in each scope, but memory pressure left little CPU progress during the elapsed time.  Both edits were restored exactly, and warning-only work on `Iter`, `NegIter`, `SharedPair`, `PushSize`, `PushTwice`, `PairFree`, and `BoxFree` remains deferred until a substantive theorem change or smaller module boundary justifies the elaboration cost.

`Project.Clob.FreshFixedArrayAt.write64_data` proves that a 64-bit write in the data region preserves the six fixed-array header words.  `ClobCancel.Spec` now applies this theorem at two copy-write sites, replacing twenty-seven lines of repeated framing proofs, while the untracked `ClobPostOnly.Append` proof contains the third matching use site and remains untouched.  Constrained `--wfail` builds completed in 3.3 seconds for `Project.Clob` and 41 seconds for `Project.ClobCancel.Spec`, with one Lean child and no warning in either checked target.

The final process check found no Lean or Lake process, and `LebU32.Iter` matched its committed contents after restoration.  The working tree still contains only the pre-existing modified `ClobPostOnly.Spec`, untracked `ClobPostOnly.Append`, and nested untracked `leanclob` repository.  No generated model, checked WASM, checked WAT, or current `postOnly` proof file changed during this maintenance.

## 2026-07-15: Recursive Public-ABI State

The expanded CLOB comparison matrix exposed a compiler error in exported natural-number recursion.  The public ABI represents a heap array by its data pointer, while the internal recursive representation carries its owner and data pointer in separate slots.  The old lowering assigned internal recursive slots positionally from public parameters, so a nested `MatchState` corrupted its book, trades, or remaining order after the first iteration.

Exported recursion now initializes separate internal carried locals from the public ABI and materializes a fresh aggregate recursive argument once before assigning its component slots.  Loop-owner trackers start at zero because function inputs are borrowed, record allocations created inside the loop, retain ownership when the next state carries the same allocation, and release an owned value when no next owner slot retains it.  Materialization remains limited to exported ABI conversions and aggregate top-level carried types, preserving the established direct lowering for byte arrays, scalars, and nonaggregate arrays.

A reduced `RecArrayState` fixture exercises two recursive iterations and checks the public owner-and-pointer conversion.  The reference-counting suite now passes 41 cases, including a two-iteration case with three allocations, no retain, one release, and one free.  The standard comparison matrix passes 340 source comparisons and 62 IR comparisons, including seven `postOnly`, five `matchFuel`, six `limit`, five `market`, and two `depth` cases.

The complete root runner passed once during implementation with 791 accepted cases, 45 rejections, 14 traps, and the full supporting test set.  After the final materialization scope was narrowed, focused compiler, reference-counting, differential, WAT, and sixteen-case Talos artifact checks passed against the final source.  The narrowing restored byte-identical `validate` and `leb_u32` artifacts and changed no checked proof input.

The default Talos gate matched all sixteen WASM and WAT pairs, then used its no-build proof check.  Seven proof targets were stale: `Project.Validate.Spec`, `Project.SharedPair.Spec`, `Project.LebU32.Iter`, `Project.LebU32.NegIter`, `Project.ClobFindBest.Model`, `Project.ClobPostOnly.Allocation`, and `Project.Runtime.Checks`.  This result reports missing or outdated build objects after cache removal; it does not report a failed theorem.

## 2026-07-15: Flat Order Reconstruction

`Project.Clob` now defines `OrderL.word` and `orderWord` as the shared flat view of one five-word order record.  `OrdersAt.orderWord_eq` projects any represented order to that view, and `OrdersAt.ofFlatWords` reconstructs the structured predicate from an indexed word equality and indexed memory bound.  These lemmas isolate the record-layout arithmetic that both cancel and the in-progress append proof had repeated.

The cancel theorem now handles its copied prefix and shifted suffix through one arbitrary field index.  The shared constructor expands that result into the five field reads and their memory bounds, removing seventy-two lines while preserving the theorem statement.  Constrained warning-failing builds completed `Project.Clob` in 2.1 seconds and `Project.ClobCancel.Spec` in 35 seconds with one Lean process and no warning.

A new tactic would add no useful proof boundary at this point.  `omega` handles the index arithmetic, `simp` handles the five concrete field projections, and `read_frames` handles read-over-write obligations.  Another helper should follow only when the completed append or matching proof reveals a second stable copy-loop or allocation postcondition beyond the flat-word lemma.

## 2026-07-15: Process Failure Diagnostics

Several JavaScript test runners assumed that a failed `spawnSync` call always returned string-valued stderr and stdout.  A launch failure returns an `error` and can leave both output values undefined, so the diagnostic path threw a property-access exception before reporting the missing compiler executable.  `tools/run-process.js` now owns synchronous launch checking, command formatting, status and signal reporting, and safe collection of optional output.

The compiler, execution, ownership, differential, WASI, and host runners now use the shared helper.  A focused test checks a missing executable with `ENOENT`, a status-seven child with specific stderr, and a successful child with ignored output streams.  `test/run_all.js` runs this test before compiler work and invokes each of its five explicit Lake targets sequentially, removing the previous multi-target command that could start concurrent Lean children.

The complete root suite passed under `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=1G`, `CPUQuota=100%`, `nice -n 10`, `ionice -c 3`, and a one-hour timeout.  It passed 3 process-error cases, 114 classifications, 10 ownership reports, 9 CLI errors, 791 accepted cases, 45 rejections, 14 traps, 41 reference-counting cases, 340 standard-Lean comparisons, 62 IR comparisons, and every remaining execution group.  Each Lake command named at most one target, and the run used the absolute compiler path inherited by every child test.

## 2026-07-15: Bounded Talos Cache Restoration

The proof cache was restored one target at a time after the shared CLOB model changed.  `Project.Runtime.Checks`, `Project.ClobPostOnly.Allocation`, and `Project.ClobFindBest.Model` completed in 1.3 to 1.7 seconds.  The deeper CLOB chain also rebuilt successfully: `ClobFindBest.Helpers` in 104 seconds, `ClobPostOnly.SearchHelpers` in 103 seconds, `ClobFindBest.Loop` in 206 seconds, `ClobPostOnly.FindBest` in 216 seconds, and the remaining model, wrapper, validity, invalid, crossing, and specification targets in 1.1 to 27 seconds.

`Project.ClobPostOnly.Append` contains 1,105 lines and one public theorem spanning roughly 870 lines after its local definitions.  Its constrained warning-failing build reached the twenty-minute timeout without a Lean diagnostic or output object.  The target combines the first allocator walk, the complete flat-word copy loop, five appended-order writes, structured `OrdersAt` reconstruction, and the second allocator walk in one elaboration unit.

`Project.Validate.Spec` reached a fifteen-minute constrained timeout without a diagnostic.  Earlier unchanged attempts had already established 30-minute and 15-minute limits for `Project.SharedPair.Spec` and `Project.LebU32.Iter`, with `Project.LebU32.NegIter` sharing the same monolithic iteration structure.  Rebuilding these unchanged targets would repeat measured work without improving the proof architecture.

The append proof needs separately compiled theorems for the first allocation and copy phase, the five-field order store and structured-book reconstruction, and the empty-trade allocation and final frame.  The shared `OrdersAt.ofFlatWords` theorem supplies the semantic boundary for the middle phase, while `FreshFixedArrayAt.write64_data` supplies its header frame.  The existing `omega`, `simp`, and `read_frames` tactics already discharge local normalization, so another tactic would not reduce the size of the elaborated store and instruction terms.

Repository instructions now prohibit retrying an unchanged target after a no-diagnostic timeout.  A later attempt must divide the proof or module, or add a verified lemma that reduces the term elaborated in the timed-out target.  The in-progress `ClobPostOnly.Spec` and untracked `ClobPostOnly.Append` files remained unchanged during cache restoration.

## 2026-07-15: Composed `postOnly` Append Proof

The successful append branch now composes four instruction-slice theorems instead of elaborating one 870-line proof.  `AppendOrderAlloc` proves the free-list scan, bump allocation, header writes, and empty copy invariant; `AppendOrderCopy` proves the flat-word loop against a prefix invariant; `AppendOrderFinish` proves the five order stores and reconstructs `OrdersAt`; and `AppendTrade` proves the empty trade-array allocation.  The public `postOnly_appended` theorem retains the exact return values, book contents, fresh-array predicates, page and global updates, and low-memory frame.

The split uses continuation-parametric statements for the first three phases.  Each theorem proves `wp` for `phaseProg ++ rest` and accepts the next phase through a semantic postcondition, which prevents `wp` simplification from expanding later instruction lists.  `FreshFixedArrayAt.write64_data`, generalized fixed-array memory initialization, `OrdersAt.ofFlatWords`, and the existing `read_frames` tactic discharge the repeated semantic obligations without a new tactic.

The generated successful branch ends before the enclosing function's three result loads.  An initial composition included those loads in `AppendTrade.appendTradeProg`, and a checked program comparison found one nested suffix of length 125 matching the first 125 instructions of the 128-instruction composition.  The trade phase now stops after setting result locals 31, 32, and 33, and its assertion records those values so `wp.imp` can prove the enclosing continuation.

Constrained warning-failing builds complete `AppendOrderCopy` in 2.3 seconds, `AppendOrderAlloc` in 6.3 seconds, `AppendOrderFinish` in 9.4 seconds, `AppendTrade` in 1.7 seconds, and the cleaned 229-line `Append` module in 14 seconds.  `Project.ClobPostOnly.Spec` then rebuilt the invalid branch in 37 seconds, the crossing branch in 45 seconds, and the aggregate module in 1.2 seconds.  Every command used the repository memory, CPU, I/O-priority, and timeout limits, and no Lean or Lake command ran concurrently.

- [x] Divide the successful append proof into compiled semantic phases.
- [x] Match each named instruction slice to the generated nested branch.
- [x] Build `Project.ClobPostOnly.Append` and `Project.ClobPostOnly.Spec` with `--wfail`.
- [ ] Compare the completed cancel and append copy invariants with the next matching update before generalizing a whole-loop theorem.

## 2026-07-15: `matchFuel` Artifact Registration

`matchFuel` is not reachable from the `postOnly` export, so its proof requires a separate byte-pinned artifact.  The accepted export has nine public `i64` parameters for fuel, the taker, two array pointers, and remaining quantity, and returns three `i64` values for the resulting book, trades, and quantity.  The temporary compiler artifact contains 6,881 WASM bytes, 95,874 WAT bytes, nineteen functions, and an exported body spanning roughly 1,850 WAT lines.

The new `clob_match_fuel` case follows the existing verifier layout.  It adds one empty Rust crate manifest, compiler-produced WASM and WAT inputs, the generated 3,871-line `Project.ClobMatchFuel.Program`, a handwritten specification shell, and a focused check script.  The shell compiles but contains no semantic theorem, so the documentation records sixteen completed specifications and one in-progress case.

The aggregate artifact gate matched all sixteen prior pairs before its proof-freshness check reported six stale modules.  Four are unchanged modules with recorded no-diagnostic timeouts: `Validate.Spec`, `SharedPair.Spec`, `LebU32.Iter`, and `LebU32.NegIter`; the other two are bounded CLOB dependencies, `ClobQuote.Step` and `ClobFindBest.Helpers`.  The unchanged timeout cases require proof division before another build, while the bounded CLOB dependencies can rebuild as later targets require them.

## 2026-07-15: `matchFuel` Source Model

The matching exports share a four-word trade layout, so `Project.Clob` now defines `TradeL`, `TradesAt`, and flat-word introduction and elimination theorems beside the existing order representation.  `Project.ClobFindBest.Model` exposes the bound on every successful search result, which the matching branches need before reading or replacing an order.  `Project.ClobMatchFuel.Model` follows the source recursion over list-backed books and trades while preserving `UInt64` arithmetic.

The model target passes a warning-failing constrained build in 2.2 seconds after its dependencies were current.  The shared additions also passed warning-failing builds when Lake rebuilt `Project.Clob` and `Project.ClobFindBest.Model`.  No generated program changed.

The partial-fill branch replaces one maker quantity while preserving every other order field.  `setQtyL_length` proves that this update preserves the book length, `setQtyL_eq_set` identifies it with a valid `List.set`, and `setQtyL_word` states the exact changed flat word.  The model passes a warning-failing constrained build in 1.3 seconds with these lemmas.

- [x] Define the shared trade value and memory representation.
- [x] Prove that a successful `findBestL` result is in bounds.
- [x] Define exact list-level book, trade, and remaining-quantity transitions.
- [x] Prove the generated scalar and search helpers for the new artifact.

## 2026-07-15: Embedded `findBest` Proof

Functions 1 through 9 in the matching artifact reproduce functions 0 through 8 in the standalone `findBest` artifact, with internal call indices increased by one.  The matching proof now covers the side, crossing, eligibility, and price helpers, the complete fuel loop, and the internal wrapper at their generated indices.  The loop uses the public `bestPrefixL_some_lt` theorem from the source model instead of retaining the copied private proof.

Warning-failing constrained builds complete the helper module in 102 seconds, the 992-line loop module in 203 seconds, and the wrapper plus specification shell in 6.1 seconds.  The loop theorem returns `optionVals (findBestL os taker)` for every represented order list and preserves the complete store.  The remaining exported proof can therefore treat the generated search call as one verified semantic step.

- [x] Prove the four pure search helpers at the matching artifact's indices.
- [x] Prove the embedded generated search loop against `findBestL`.
- [x] Prove the internal wrapper and import it from the specification shell.
- [ ] Divide the exported matching loop at its three early-exit branches.

## 2026-07-15: Zero-Fuel Matching Exit

The first exported-function theorem proves that zero public fuel returns the input book pointer, trade pointer, and remaining quantity without changing the store.  Its loop invariant records the relevant locals, the zero done flag, and the exact nine-parameter and seventy-six-local frame lengths.  The frame lengths let the final return suffix simplify local assignments without expanding the complete generated frame.

The warning-failing constrained build completes `Project.ClobMatchFuel.EarlyExit` in 19 seconds.  The proof selects the generated false branch after the fuel test, follows its break from the enclosing block, and proves the final three-value ABI exactly.  The same frame facts will support the zero-remaining and no-maker exits, which each enter the loop once before setting the done flag.

- [x] Prove the zero-fuel exit over the exact public ABI.
- [x] Prove the zero-remaining exit for nonzero fuel.
- [x] Prove the no-maker exit through the verified search wrapper.

The zero-remaining theorem passes a warning-failing constrained build in 46 seconds.  Its two-phase invariant uses the done flag as a natural-number measure and proves the generated re-entry decreases that measure from one to zero.  Both phases preserve the complete store and return the input state pointers and zero remaining quantity.

The no-maker theorem extends the invariant with the stable taker fields, the wrapper's zero argument, and the empty operand stack.  It calls the verified function-9 search theorem, reduces the `none` option ABI, and returns the input state without changing the store.  The complete early-exit module passes a warning-failing constrained build in 79 seconds.

## 2026-07-15: Fixed-Array Release Semantics

The generated `matchFuel` module's functions 15 through 18 are definitionally equal to the shared allocator, reset, retain, and release definitions.  `Project.Runtime.Checks` now pins those equalities, and its warning-failing constrained build completes in 2.2 seconds.  Function 18 therefore uses the module-generic runtime specifications instead of an artifact-specific copy of the release proof.

The existing release theorems did not cover the arrays used by matching.  `release_frees_fresh_raw` requires kind 0, while `release_frees_tree` models kind-1 slot objects; CLOB books and trades are kind-2 fixed arrays.  The runtime's kind-2 branch reads the array length, stride, and pointer mask, walks both dimensions, releases each masked field, and then adds the root to the free list.

`Project.Runtime.FixedArraySpec.release_frees_fixed_array_zero_mask` proves the shared kind-2 case used by CLOB arrays.  Two natural-number variants prove termination of the generated nested loops, and the zero mask proves that the walk neither reads element words nor calls release recursively.  The theorem returns the exact refcount write, free-list link, release and free counter increments, and unchanged remaining globals; its warning-failing constrained build completes in 7.9 seconds.  `Project.ClobMatchFuel.Allocation.func18_frees_fixed_array_zero_mask` specializes the theorem to the generated module and passes a warning-failing constrained build in 1.9 seconds.

## 2026-07-15: First-Fit Allocator Model

`Project.Runtime.FreeList` models the state consumed by the shared `rcAllocPayload` instruction builder.  `takeFirstFit` selects the first node with adequate capacity and proves the selected capacity, membership, and one-node length change.  `FreeListAt` records each node's zero refcount, capacity, next link, memory bounds, and separation from its tail, while its frame theorem preserves those facts across unrelated writes.

The compiler already emits every inline allocation through the single `LeanExe.Wasm.Binary.rcAllocPayload` builder.  A compiler change to call the exported allocator would change completed artifacts without eliminating source duplication.  The matching proof will instead verify the current first-fit and bump paths against `FreeListAt`, then reuse that semantic result at its four generated array-allocation sites.

The free-list model passes a warning-failing constrained build in 1.7 seconds.  It introduces no axiom, tactic, or dependency and contains no artifact-specific local indices.  The next theorem must connect one generated allocation walk to `takeFirstFit` before the matching branch proof depends on this model.

`takeFirstFitFrom` retains the predecessor pointer, selected node, successor pointer, and remaining list needed to describe the generated unlink writes.  Its projection equals `takeFirstFit`, so capacity, membership, and one-node length results remain properties of one selection model.  `FreeListAt` now proves that every represented root is nonzero and that separated node regions give duplicate-free roots, which permits a linked-list traversal measure based on the current node's position rather than its address.

`Project.ClobMatchFuel.BookAllocSearch.bookAllocSearchProg_no_fit` proves the full generated book-allocation search when no represented node has enough capacity.  The invariant splits the original free list into a visited prefix and represented suffix, and `scanRemaining_suffix` identifies the loop measure with the suffix length at each cursor.  The theorem preserves the store, returns the zero cursor required by the bump path, and passes a warning-failing constrained build in 3.6 seconds.

An aggregate `Project.ClobMatchFuel.Spec` import check spent most of its two-minute limit rebuilding the unchanged `Helpers` target, completed that dependency, and reached the timeout while rebuilding `FindBest` without a Lean diagnostic.  The unchanged aggregate target will not run again until its remaining dependency objects are current or a substantive proof change reduces that boundary.  The new search target and its modified shared free-list dependency both pass their focused warning-failing builds.

`takeFirstFitFrom_some_decompose` gives the exact successful-selection split into skipped nodes, the selected node, and its successor tail.  It identifies the predecessor pointer through `previousRoot`, identifies the successor and remaining list, and proves that every skipped node was too small.  The shared free-list target passes a warning-failing constrained build in 1.7 seconds with this result.

## 2026-07-15: First-Fit Unlink Semantics

`FreeNode.read64_write64_disjoint` reduces header read-over-write obligations to represented region separation, and `FreeListAt.frame_write64_disjoint` applies that result to a complete retained free list.  `FreeListAt.unlink_takeFirstFitFrom` now proves the exact successful first-fit deletion: a head selection leaves the successor list unchanged, while a later selection writes the selected successor to the predecessor's next field.  `FreeListAt.takeFirstFitFrom_node_disjoint` proves that subsequent initialization writes inside the selected node preserve every retained free-list node.

The proof identifies a nonempty skipped prefix through `List.dropLast_append_getLast`, then applies one adjacent-node unlink theorem.  This structure avoids assumptions about pointer order and uses only the region separation stored by `FreeListAt`.  The warning-failing constrained `Project.Runtime.FreeList` build completes in 2.3 seconds.

## 2026-07-15: Successful Book Allocation Search

`Project.ClobMatchFuel.BookAllocFit.bookAllocSearchProg_fit` proves the exact generated first-fit traversal for every successful `takeFirstFitFrom` result.  A search-state invariant divides the too-small prefix into visited and remaining nodes, while a completed state records the selected root and the post-allocation store.  The measure uses `scanRemaining` until local 81 receives the nonzero selected root, then permits the generated re-entry to exit through its result check.

The head case updates global 1 to the selected successor, while the non-head case writes that successor to the predecessor's next field.  Both cases write the six generated kind-2 fixed-array header words and expose the exact final locals through a continuation-parametric theorem.  `freeListAt_bookAllocFitMem` composes the shared unlink and disjoint-write frame theorems to preserve `FreeListAt` for every remaining node, and the warning-failing constrained module build completes in 7.8 seconds.

The changed `Project.ClobMatchFuel.Spec` import target reached its three-minute constrained timeout without output or a Lean diagnostic.  The focused `BookAllocFit` target had already passed, and no Lean or Lake process remained after the timeout.  The aggregate target will not run again until another source change or a smaller verified boundary reduces its elaboration work.

## 2026-07-15: Fixed-Array Header Boundary

`Project.Clob.fixedArrayHeaderMem` names the six metadata writes that generated fixed-array allocations perform before writing the array length.  `fixedArrayMem` now composes that header transformation with its existing length write, preserving its seven-write behavior.  `fixedArrayHeaderMem_spec` proves the resulting `FreshFixedArrayAt` predicate and gives the book-allocation bump branch a semantic boundary that the later trade allocation can reuse.

The warning-failing constrained `Project.FixedArrayAllocation` build completes in 2.3 seconds.  The helper adds no dependency, axiom, or tactic.  Its proof uses the existing `read_frames` tactic after normalizing the six header addresses.

## 2026-07-15: Book Allocation Bump Path

`Project.ClobMatchFuel.BookAllocBump.bookAllocBumpProg_spec` proves the generated no-result allocation branch from its local-81 test through the heap-top update and six header stores.  Its assumptions state the generated eight-byte minimum capacity, exact nonwrapping top arithmetic, sufficient existing pages, the Wasm page limit, and global 0.  The postcondition records `fixedArrayHeaderMem`, the new global 0 value, the payload root, the computed page count, and the overwritten local frame.

`bookAllocNoFitProg_spec` composes that result with `bookAllocSearchProg_no_fit`, retaining the final predecessor as an irrelevant quantified local.  `freshOrderArrayAt_bookAllocBumpStore` proves the fresh kind-2 header, while `freeListAt_bookAllocBumpStore` preserves represented free nodes whose allocated regions end at or below the old heap top.  The warning-failing constrained `Project.ClobMatchFuel.BookAllocBump` build completes in 6.4 seconds, and the unchanged aggregate target was not retried after its recorded timeout.

## 2026-07-15: Erased Order Reconstruction

`OrdersAt.eraseIdx_ofFlatWords` reconstructs an erased order array from an unchanged flat prefix and a suffix shifted left by one five-word order.  It also consumes the output length word and all target read bounds, then uses the source `OrdersAt` predicate to identify each retained field.  The theorem factors the list-index and five-field reasoning shared by the completed cancel proof and the full-fill `matchFuel` branch.

The warning-failing constrained `Project.Clob` build completes in 2.6 seconds.  The helper builds on `OrdersAt.ofFlatWords` and adds no tactic or memory-layout assumption.  The generated copy loops remain responsible for proving the prefix, suffix, and target-bound hypotheses.

`flatWordsRegion` and `flatWordsDisjoint` state the nonwrapping memory separation used while copying one fixed-width array into another.  `OrdersAt.frame_write64_flatWordsDisjoint` proves that one target-word write preserves the complete source order representation, and `OrdersAt.orderWord_bound` projects the corresponding source read bound.  These results let a generated copy-loop invariant retain `OrdersAt` directly instead of carrying a separate byte-level source frame.

The extended warning-failing constrained `Project.Clob` build completes in 3.4 seconds.  The flat-word separation definition remains in the source model, avoiding a dependency from CLOB representations to runtime release-tree machinery.  The theorem requires explicit source and target nonwrapping bounds and a target word within its declared region.

The frame theorem now accepts every target flat-word slot from the length word through the final data word.  This generalization covers the generated output-length store and both subsequent copy loops with one memory-separation result.  The warning-failing constrained `Project.Clob` build completes in 4.4 seconds.

`OrdersAt.orderWord_eq_flat` and `OrdersAt.orderWord_bound_flat` recover a structured field value and its memory bound from any flat index below the represented word count.  Their proofs use the standard natural-number division theorems instead of arithmetic search over quotient and remainder.  After that change, the warning-failing constrained `Project.Clob` build completes in 3.5 seconds within its default heartbeat budget.

`Project.ClobMatchFuel.BookErasePrefix.erasePrefixProg_spec` proves the full-fill branch from the allocation counter increment through the output-length store and generated prefix loop.  Its invariant preserves the allocated header and source `OrdersAt` representation for either allocator outcome, using explicit source-target region separation rather than heap-order assumptions.  The warning-failing constrained module build completes in 3.9 seconds.

`Project.ClobMatchFuel.BookEraseSuffix.eraseSuffixProg_spec` proves the shifted suffix loop, the returned allocated root, and the resulting `OrdersAt st target (os.eraseIdx i)` predicate.  The invariant retains completed prefix words while copying each source word after the removed five-word order into its destination.  The warning-failing constrained module build completes in 6.4 seconds.

`Project.ClobMatchFuel.BookReplaceStore` names the five word stores used to replace a copied maker order and proves that they produce `Model.setQtyL os i qty`.  Its theorems preserve every other order word, all represented memory bounds, and the allocated fixed-array header.  The warning-failing constrained module build completes in 2.3 seconds.

`Project.ClobMatchFuel.BookReplaceCopy.replaceCopyProg_spec` proves the partial-fill branch from its post-allocation frame through the allocation-counter increment, output-length store, and complete flat-word copy.  The theorem accepts either allocator outcome through an arbitrary separated target and reconstructs `OrdersAt st target os` before the replacement stores.  The warning-failing constrained module build completes in 4.8 seconds.

`Project.ClobMatchFuel.BookReplaceFinish.replaceFinishProg_spec` proves the five generated field stores and returned root that finish the partial-fill book update.  It identifies the exact memory transformation with `replaceOrderStore`, then supplies the `Model.setQtyL` order representation and preserved fixed-array header to its continuation.  The warning-failing constrained module build completes in 4.3 seconds.

`TradesAt.tradeWord_bound`, `tradeWord_eq_flat`, and `tradeWord_bound_flat` give trade arrays the same structured and arbitrary flat-index projections as order arrays.  The copy theorem can now derive each source load bound and recover its source field without duplicating quotient-and-remainder arithmetic.  The warning-failing constrained `Project.Clob` build completes in 3.0 seconds.

`flatWordsDisjoint_address` extracts the byte-range consequence shared by separated order and trade arrays, and the existing order frame theorem now uses it.  `TradesAt.frame_write64_flatWordsDisjoint` preserves a complete source trade representation across every write within a separated target array.  The warning-failing constrained `Project.Clob` build completes in 4.2 seconds.

## 2026-07-15: Matched-Trade Prefix Copy

`Project.ClobMatchFuel.TradeAppendCopy.tradeCopyProg_spec` proves the generated allocation-counter update, output-length store, and complete copy of the existing trade words into a fresh array.  Its invariant preserves the source `TradesAt` predicate, destination header, destination length, and every copied flat word under explicit nonwrapping and separation assumptions.  The warning-failing constrained module build completes in 4.1 seconds after its imported targets are current.

`Project.ClobMatchFuel.TradeAppendStore` defines the four-word append independently of generated local indices and proves its read behavior, extended `TradesAt` representation, and fixed-array-header frame.  `TradeAppendFinish.tradeFinishProg_spec` applies those results to the exact generated stores and supplies the fresh root to an arbitrary continuation.  Warning-failing constrained builds complete the semantic store module in 3.8 seconds and the instruction theorem in 5.4 seconds.

The successful-fit and bump allocation stores now take the fixed-array element stride, with the existing book names retained as stride-five wrappers.  Shared theorems prove retained free-list representation and fresh fixed-array headers for any stride, so the remaining trade allocator can use stride four without copying the memory proof.  Warning-failing constrained builds complete `BookAllocFit` in 12 seconds and the dependent `BookAllocBump` target in 8.7 seconds.

`PartialBookAllocSearch`, `PartialBookAllocFit`, and `PartialBookAllocBump` prove the partial-fill allocator at its generated scratch locals 79 through 84.  The control proofs retain the prior first-fit traversal and bump arithmetic but use the shared stride-five allocation stores instead of copying their memory semantics.  Warning-failing constrained builds complete the three modules in 3.6, 8.6, and 7.2 seconds.

`TradeAllocSearch`, `TradeAllocFit`, and `TradeAllocBump` prove the common trade allocator at its generated scratch locals 78 through 83.  The program writes stride four, and both allocator outcomes use the shared stride-parameterized stores, fresh-header theorems, and free-list frames.  Warning-failing constrained builds complete the three modules in 3.6, 9.1, and 6.6 seconds.

`fixedArrayBytesU_toNat` connects the modular fixed-array capacity calculation to its natural-number byte count through explicit intermediate bounds.  `fixedArrayBytesU_round` proves that the generated add-seven, divide-eight, multiply-eight sequence leaves this byte count unchanged.  The shared `Project.Clob` target passes a warning-failing constrained build in 4.5 seconds.

`BookAllocPrepare`, `PartialBookAllocPrepare`, and `TradeAllocPrepare` prove the generated capacity rounding, minimum-capacity check, zeroed result and predecessor, and free-list-head initialization at each allocator layout.  Each theorem ends at the corresponding search frame while preserving the untouched capacity and next-link scratch values through explicit local-list equality.  Warning-failing constrained builds complete the erased-book, partial-book, and trade modules in 3.3, 2.7, and 2.9 seconds.

`TradeAlloc.tradeAllocProg_spec` composes trade capacity preparation with the complete first-fit search and bump fallback.  A case split on `takeFirstFitFrom` supplies the exact stride-four fit store and selected `FreeChoice`, or the exact bump store and final predecessor, to an arbitrary continuation.  The warning-failing constrained module build completes in 2.2 seconds.

`BookAlloc.bookAllocProg_spec` and `PartialBookAlloc.partialBookAllocProg_spec` apply the same allocation composition to the two stride-five book layouts.  Their fit paths prove that the generated bump conditional skips on the selected nonzero root, while their no-fit paths execute the verified bump allocator.  Warning-failing constrained builds complete both composition modules in 2.2 and 2.0 seconds.

## 2026-07-15: Fixed-Array Region Frames

`fixedArrayRegion` covers the six-word allocation header and the payload capacity recorded in that header.  `FreshFixedArrayAt.frame_region`, `OrdersAt.frame_region`, and `TradesAt.frame_region` preserve the corresponding representations when memory pages agree and every byte in that region is unchanged.  The warning-failing constrained `Project.Clob` build completes in 4.8 seconds.

## 2026-07-15: Live-Array Allocator Frames

`AllocatorFrame` defines refcount-one order and trade arrays by combining their fixed-array headers with their represented contents.  A free-list separation predicate covers the source's complete allocation region, so the successful-fit theorem preserves the source across both the predecessor unlink and the selected node's six header writes.  The bump theorem uses below-heap byte preservation, and a common interval lemma derives the payload separation required by each copy loop; the warning-failing constrained target completes in 1.5 seconds after its dependencies are current.

## 2026-07-15: Copy Outside-Region Frame

`MemEqOutsideFlatWords` states byte equality outside one fixed-width payload, and its write theorem preserves that equality for every declared payload slot.  The matched-trade copy invariant now carries this frame through the output-length store and every copied trade word, allowing later branch composition to recover unrelated live arrays.  The warning-failing constrained `TradeAppendCopy` build completes in 3.7 seconds after its dependencies are current.

The partial-fill book copy now carries the same frame through its length store and complete five-word-order copy.  The full-fill prefix and shifted-suffix invariants preserve one frame relative to the allocator outcome store across both loops.  Warning-failing constrained builds complete `BookReplaceCopy` in 4.3 seconds, `BookErasePrefix` in 5.4 seconds, and `BookEraseSuffix` in 7.2 seconds after their dependencies are current.

## 2026-07-15: Trade Allocation and Copy Composition

`TradeAllocCopy.tradeAllocCopyProg_spec` composes capacity preparation, first-fit search or bump allocation, and the complete old-trade prefix copy.  Each outcome derives the fresh target header, exact payload bounds, source-target separation, preserved refcount-one source trade array, and outside-payload byte frame before entering its own continuation.  The outcome-specific continuations retain either the selected `FreeChoice` or the bump predecessor, and the warning-failing constrained target completes in 4.1 seconds after its dependencies are current.

## 2026-07-15: Partial Book Allocation and Copy

`PartialBookAllocCopy.partialBookAllocCopyProg_spec` composes the partial-fill stride-five allocator with the complete source-book copy at its generated local layout.  Its fit and bump outcomes supply the fresh target header, exact target `OrdersAt`, preserved refcount-one source book, outside-payload byte frame, and the allocator data required by later replacement and release steps.  The warning-failing constrained target completes in 3.8 seconds after its dependencies are current.

## 2026-07-15: Erased-Book Copy Composition

`BookErasePrefix.erasePrefixProg_spec` now gives its continuation the completed-prefix equality directly.  `BookAllocErase.bookCopiesProg_spec` uses that fact to compose the prefix and shifted-suffix loops, preserving one outside-payload frame and reconstructing `OrdersAt (os.eraseIdx i)` at the returned target.  The warning-failing constrained composition target completes in 1.9 seconds after its dependencies are current.

`BookAllocErase.bookAllocEraseProg_spec` places the full-fill stride-five allocator before the shared two-loop theorem.  Both allocator outcomes derive the exact target bounds and separation, preserve the refcount-one source book, and return the erased book representation while retaining fit or bump outcome data.  The warning-failing constrained target completes in 5.3 seconds after its dependencies are current.

## 2026-07-15: Final Store Frames

`BookReplaceFinish.replaceFinishProg_spec` now preserves byte equality outside the complete destination book payload through its five replacement stores.  `TradeAppendFinish.tradeFinishProg_spec` preserves the analogous frame through its four appended-trade stores.  Warning-failing constrained builds complete the book target in 4.0 seconds and the trade target in 4.7 seconds after their changed dependencies are current.

## 2026-07-15: Allocation-Copy Result Bounds

The partial-book and trade allocation-copy theorems now pass each target's lower bound, nonwrapping payload bound, current-memory fit bound, and pre-copy owned source array to both outcome continuations.  Their proofs already established these facts, and the stronger interfaces retain them for final stores and source release.  Warning-failing constrained builds complete `PartialBookAllocCopy` in 3.0 seconds and `TradeAllocCopy` in 3.9 seconds.

## 2026-07-15: Final Update Composition

`MemEqOutsideFlatWords.fixedArray_bytes` converts an outside-target-payload frame into byte equality on a disjoint fixed-array allocation region.  Order and trade ownership corollaries apply the existing header and content frame theorems, and the warning-failing constrained `AllocatorFrame` build completes in 1.7 seconds.  The result preserves a source or unrelated live array through completed destination writes without repeating byte-address arithmetic.

`FreeListAt.frame_outsideFlatWords` preserves a represented free list across completed payload writes when every retained free-node region is disjoint from the destination payload.  It derives equality for the reference-count, capacity, and next-pointer reads through `read64_congr`, so branch proofs need only the existing outside-payload frame.  The warning-failing constrained `AllocatorFrame` build completes in 3.7 seconds after its dependencies are current.

Allocator outcome lemmas now identify globals 0 and 1 after either a selected-node allocation or a heap bump.  Companion fit and bump theorems preserve the resulting free-list representation through a completed payload write, using selected-node separation or the free-nodes-below-heap bound.  The warning-failing constrained `AllocatorFrame` build completes in 2.6 seconds after its dependencies are current.

`PartialBookUpdate.partialBookUpdateProg_spec` composes partial-book allocation, complete copying, and the five quantity-replacement stores for both allocator outcomes.  `TradeAllocAppend.tradeAllocAppendProg_spec` composes trade allocation, prefix copying, and the four appended-trade stores with the same outcome data.  Warning-failing constrained builds complete the new modules in 7.4 and 6.7 seconds after their changed dependencies are current.

The partial-book and trade-update continuations now retain the final page count and exact global-list update already carried by their copy invariants.  These facts expose the post-allocation heap top, free-list head, and allocation counter needed by the following allocator and release block.  Warning-failing constrained builds complete `PartialBookUpdate` in 7.7 seconds and `TradeAllocAppend` in 6.9 seconds after their dependencies are current.

`FullTradePrepare.fullTradePrepareProg_spec` proves the generated bridge from the full-fill book result to the common trade allocator input.  It checks the book length, matched maker identifier, price, quantity, and old trade length before producing the exact trade-allocation locals.  The warning-failing constrained module build completes in 7.3 seconds after its dependencies are current.

`FullTradeFinish.fullTradeFinishProg_spec` records the fresh trade root and checks the matched maker quantity before computing the next remaining quantity.  Its exact local frame ends at the first generated release guard with an empty value stack.  The warning-failing constrained module build completes in 3.6 seconds after its dependencies are current.

## 2026-07-15: Release Transformations

`Allocation.fixedArrayReleaseMem` and `fixedArrayReleaseGlobals` name the exact memory and global-list results of freeing a refcount-one zero-mask fixed array.  `func18_frees_fixed_array_zero_mask` now states its existing runtime result with those definitions, without changing its assumptions or proof.  The warning-failing constrained `Allocation` build completes in 2.8 seconds.

`ReleaseFrame.fixedArrayReleaseMem_bytes` proves that the two release header writes preserve every byte in a disjoint region.  Its ownership corollaries preserve complete order and trade arrays, while `freeListAt_fixedArrayReleaseMem` constructs the released node at the head of the retained free list.  The module also proves root inequality from disjoint allocation regions and from order-versus-trade stride headers, and its warning-failing constrained build completes in 2.2 seconds.

`ReleaseOld.releaseOldValuesProg_calls` proves the generated alias guards and both release calls parametrically over their two `TerminatesWith` results.  The theorem covers local 19 against the new book and trade roots, then local 20 against all three prior roots, while returning the unchanged local frame to its continuation.  Its warning-failing constrained module build completes in 2.6 seconds.

`ReleaseOld.releaseOwnedArraysProg_spec` instantiates both calls for four pairwise separated owned arrays and a represented free list.  It preserves the replacement book and trade arrays while adding the consumed arrays as two new free-list heads.  The warning-failing constrained module build completes in 3.3 seconds after its dependencies are current.

`ReleaseOld.releaseOldValuesProg_none` proves that the generated guard block makes no calls when both loop-owner trackers are zero, while `releaseOldValuesProg_trade_only_calls` proves the single-call path when only the prior trade array is tracked.  `releaseTrackedTradeProg_spec` instantiates that call with the fixed-array release theorem, preserves the replacement book and trade arrays, and adds the prior trade region to the represented free list.  The warning-failing constrained `ReleaseOld` build completes in 4.7 seconds with all three interfaces.

`FullTransition.fullTransitionProg_spec` proves the sixty-six generated instructions that copy a completed full-fill result into the recursive carried state.  Its result frame records the decremented fuel, replacement owner-and-pointer pairs, remaining quantity, fresh trade tracker, and the compiler's conditional book tracker.  The warning-failing constrained module build completes in 37 seconds after its dependency is current.

`PartialBookPrepare.partialBookPrepareProg_spec` proves the partial-fill bridge from the selected-maker state to the replacement-book allocator inputs.  It reads all five maker fields from the represented source book, computes the reduced maker quantity, and records the source length and flat-word count.  The warning-failing constrained module build completes in 17 seconds after its dependencies are current.

`PartialTradePrepare.partialTradePrepareProg_spec` consumes the replacement-book root, records it as the branch result, and prepares the existing trade array for allocation and append.  It reads the maker identifier and price from the represented source book and uses the remaining taker quantity as the matched quantity.  The warning-failing constrained module build completes in 5.5 seconds after its dependencies are current.

`PartialFinish.partialFinishProg_spec` proves the seven assignments after the partial-fill trade append.  It records the fresh trade root, sets the result's remaining quantity to zero, and sets the loop's done flag.  The warning-failing constrained module build completes in 1.4 seconds after its dependency is current.

`PartialBookUpdate.partialBookUpdateProg_spec` and `TradeAllocAppend.tradeAllocAppendProg_spec` now give both allocator continuations the final represented free list and exact heap-top and free-list-head globals.  Their bump preconditions state that each represented free node lies below the old heap top, which the bump frame needs and the prior interfaces did not expose.  Warning-failing constrained builds complete the strengthened book and trade modules in 13 and 12 seconds after their dependencies are current.

`TradeAllocAppend.tradeAllocAppendProg_spec` now preserves one live owned order array through either trade-allocation outcome and the completed trade payload writes.  The fit proof uses separation from the represented free list, while the bump proof uses the array's below-heap bound.  The warning-failing constrained module build completes in 13 seconds with this stronger interface.

`PartialTradeUpdate.partialTradeUpdateProg_spec` composes partial trade preparation, both trade allocator outcomes, the copy and append stores, and result finalization.  Each outcome returns the replacement book and appended trade arrays with the represented free list and exact allocator globals, including the incremented allocation counter.  The warning-failing constrained module build completes in 13 seconds after its dependencies are current.

`takeFirstFitFrom_some_remaining_mem` proves that every node retained after a successful first-fit search belonged to the input free list.  The proof derives membership from the established search decomposition, and later allocator compositions can use it to restrict separation and below-heap predicates.  The warning-failing constrained `Project.Runtime.FreeList` build completes in 3.5 seconds.

`fixedArrayAllocFitStore_pages` and `fixedArrayAllocBumpStore_pages` state that either allocator store preserves the memory-page count.  The proofs reduce predecessor unlinking and fixed-array header initialization to the existing page-preservation theorem for `write64`.  The warning-failing constrained `AllocatorFrame` build completes in 2.5 seconds after its rebuilt dependencies are current.

`PartialBranch.partialBranchProg_spec` composes the complete partial-fill branch across all four book-and-trade allocator outcome pairs.  It preserves the source book and trade arrays through the first allocation, derives the second allocation's free-list separation and below-heap bounds, and returns the reduced book, appended trades, represented free list, and exact allocator globals.  The warning-failing constrained module build completes in 6.0 seconds after its dependencies are current.

`FullBookUpdate.fullBookUpdateProg_spec` wraps erased-book allocation and both copy loops with ownership and allocator-state results.  Each allocator outcome returns the erased book, preserved source book and trades, outside-payload frame, page equality, represented free list, and globals 0 through 2.  The warning-failing constrained module build completes in 7.4 seconds after its dependencies are current.

`FullTradeUpdate.fullTradeUpdateProg_spec` composes full-fill trade preparation, either trade allocator outcome, the complete copy and append stores, and remaining-quantity finalization.  Each outcome preserves the replacement and source books, returns the appended trade array and represented free list, and records the exact recursive carry and allocator globals.  The warning-failing constrained module build completes in 9.5 seconds after its dependencies are current.

The full-fill trade update now also preserves the source trade array through the appended payload writes.  The fit proof uses the selected free node's separation from the source allocation, while the bump proof uses the source allocation's old-heap bound.  The warning-failing constrained `FullTradeUpdate` build completes in 10 seconds with the stronger continuation interface.

`FullBranch.fullBranchProg_spec` composes the erased-book and appended-trade updates across all four allocator-outcome combinations.  It restricts free-list invariants after a book fit, advances live-array bounds after a book bump, and preserves both source arrays for the release block.  The warning-failing constrained module build completes in 10 seconds after its dependencies are current.

Allocator global-frame lemmas now preserve every index other than index 1 for a fit and index 0 for a bump.  The full trade and branch continuations use them to retain release counters 4 and 5 through both allocations and each final payload store.  Warning-failing constrained builds complete `AllocatorFrame` in 2.3 seconds, `FullTradeUpdate` in 12 seconds, and `FullBranch` in 15 seconds after their dependencies are current.

The full trade update now returns page preservation and separates the source trade allocation from both replacements and the final represented free list.  `FullBranch` derives the book separation before invoking that theorem and composes page equality across both allocations.  Warning-failing constrained builds complete `FullTradeUpdate` in 13 seconds and the release-ready `FullBranch` in 14 seconds after their dependencies are current.

Replacement-array bounds now travel with the full-fill result, and the release theorems require content bounds rather than stronger unused capacity bounds for arrays they preserve.  `FullReleaseTransition` composes the two reachable tracker cases with either no release or one tracked-trade release, then invokes the verified recursive local transition.  Its warning-failing constrained target completes in 1.7 seconds after `FullTransition` rebuilds in 35 seconds.

Release-global lemmas identify the new free-list head and release counters while preserving every unrelated global.  `FullStep.fullStepProg_spec` composes all four allocation outcomes with both reachable tracker states, the optional tracked-trade release, and the recursive local transition.  Its result retains the replacement arrays, represented free list, allocator globals, adjusted release counters, and exact recursive local frame, and its warning-failing constrained build completes in 16 seconds after its dependencies are current.

`PartialTradeUpdate.partialTradeUpdateProg_spec` and `PartialBranch.partialBranchProg_spec` now preserve globals 4 and 5 across both allocator outcomes.  The proofs apply the general fit and bump global-frame lemmas at each allocation and retain the exact unchanged release counters in the completed partial result.  Warning-failing constrained builds complete the strengthened trade update in 12 seconds and the partial branch in 15 seconds after their dependencies are current.

`LoopControl` isolates the generated outer-loop guard and result epilogue.  Its theorems cover the zero-fuel, completed, and running guard outcomes and both epilogue selections, including the exact local updates made when the loop exits without a completed branch result.  The warning-failing constrained module build completes in 4.4 seconds.

The `matchFuelL` model now has named equations for its zero-remaining, no-maker, full-fill, and partial-fill branches.  A single induction proves that matching never increases the book length and increases the trade length by at most the supplied fuel.  The warning-failing constrained model build completes in 1.7 seconds.

The full trade update and full branch now return replacement allocation bounds, heap monotonicity, free-list separation, and a below-heap bound for every retained free node.  `ReleaseFrame` provides reusable lemmas that preserve separation and node bounds when a released allocation becomes the new free-list head.  `FullStep.fullStepProg_spec` carries those facts and page preservation through either reachable tracker state, and its warning-failing constrained build completes in 19 seconds after the changed dependencies rebuild.

`LoopControl.CompletedResultAt` generalizes the result epilogue over the returned remaining quantity, while retaining the partial-fill theorem as a direct corollary.  `Iteration` gives exact frames for the generated early-completion assignments and the full-fill preparation slice, including the no-wrap equalities for erased length, prefix words, and suffix words.  Warning-failing constrained builds complete `LoopControl` in 4.6 seconds and `Iteration` in 4.2 seconds after their dependencies are current.

`Iteration.dispatchProg_spec` composes the generated remaining-quantity checks, embedded `findBest` call, no-maker completion, selected-maker quantity read, and full-versus-partial dispatch.  `zeroIffPost` names the exact continuation for a zero-arity WebAssembly `if`, and `dispatchBranchPost` composes the three enclosing branch levels without assuming that a branch body cannot break.  A constrained warning-failing `FindBest` dependency rebuild completed in 205 seconds, its wrapper completed in 3.0 seconds, and the final focused `Iteration` build completed in 13 seconds with those dependencies current.

`FullTradeUpdate`, `FullBranch`, and `FullStep` now bound post-step global 0 by the prior heap top plus the capacities of any bump allocations.  A full step advances by at most 96 header bytes, `orderArrayBytes (os.length - 1)`, and `tradeArrayBytes (ts.length + 1)`; fit outcomes consume none of that allowance, while bump outcomes use the existing no-wrap equalities.  Warning-failing constrained builds complete the changed trade, branch, and step targets in 19, 25, and 23 seconds, respectively.

`Budget.stepBytes` gives one conservative book-and-trade allocation allowance from fixed source length limits.  Its lemmas prove fixed-array monotonicity, bound full and partial updates, expose one step of capacity from nonzero fuel, preserve the remaining budget across a decrement, and normalize a bounded allocator bump to natural-number addition.  The warning-failing constrained `Project.ClobMatchFuel.Budget` build completes in 2.4 seconds.

`Initialization.initProg_spec` proves the exported function's parameter copies, zeroed owner trackers, and cleared completion flag against one exact recursive frame.  The theorem uses explicit length and input-value premises because simplifying `func14Def.toLocals` inside every instruction expanded the complete generated body and produced a 39-second type mismatch; the generic frame compiles without that expansion.  The warning-failing constrained initialization target completes in 3.1 seconds after its dependencies are current.

The allocator scratch predicate records the four high local slots whose `i64` types the next generated iteration requires.  Both trade-allocation outcomes establish the predicate, `FullBranch` preserves it across all allocator combinations, and `FullStep.allocScratchAt_fullTransitionFrame` proves that the recursive transition leaves those slots unchanged.  Warning-failing constrained builds complete `FullTradeUpdate`, `FullBranch`, and `FullStep` in 19, 22, and 20 seconds, respectively.

`Model.fullFillCountL` counts the full-fill source branches that affect the generated release counters.  Its named equations follow the same four branch cases as `matchFuelL`, and `fullFillCountL_le` bounds the count by the supplied fuel.  The warning-failing constrained model build completes in 1.8 seconds.

The embedded search theorems now quantify over the loop-carried book owner passed through functions 9 and 8.  Function 8 copies that owner into two scratch locals without inspecting it, so its frame and reusable step lemma preserve the value while the source search result remains unchanged; the iteration quantity frame records the same owner.  Constrained warning-failing builds complete the expensive `FindBest` proof in 245 seconds, `FindBestWrapper` in 4.7 seconds, and `Iteration` in 12 seconds after the model-dependent modules are current.

`FullStep.fullTransitionFrame_oldBookTracker_zero` proves that the recursive transition keeps the old-book tracker at zero when the fresh book differs from zero and the prior trade tracker.  The no-tracker branch derives both inequalities from the fresh-book lower bound, while the tracked branch derives root inequality from the established allocation-region separation.  The strengthened `FullStep` continuation returns this exact local fact, and its warning-failing constrained build completes in 18 seconds.

`LoopInvariant` defines one context for the initial source state, counters, page count, and heap limit, plus separate data and fact records for running and completed loop states.  The running facts cover recursive locals, source and full-fill progress, length bounds, owned arrays, free-list separation, allocator globals, exact counters, page bounds, and remaining allocation budget; the completed facts state the exact source result, owned output arrays, represented free list, and public counters.  The warning-failing constrained module build completes in 1.8 seconds.

`LoopBounds.StepBounds` derives the shared numeric premises for either full-fill or partial-fill allocation pair from a running invariant and nonzero fuel.  The record includes array lengths, fixed-array byte normalizations, unsigned allocation tops, 32-bit no-wrap bounds, and current-page fit bounds, so branch composition does not repeat the same arithmetic.  The warning-failing constrained module build completes in 3.4 seconds.

`Iteration.dispatchProg_spec` now passes its known source-branch premise to each continuation.  A stop reports zero remaining quantity or a missing maker, while a full or partial update reports nonzero remaining quantity in addition to the search and quantity comparisons.  The warning-failing constrained module build completes in 13 seconds.

`LoopProgress` proves the residual source equations for stopped, partial-fill, and full-fill states recorded by the loop invariant.  It also normalizes the modular allocation counter after an appended trade and the conditional release counter after a full fill.  The warning-failing constrained module build completes in 1.6 seconds.

`LoopCompletion.of_stop` and `LoopCompletion.of_partial` construct the completed invariant from the two terminating dispatcher outcomes.  They prove the exact source result, owned output arrays, represented free list, allocator globals, and normalized allocation and release counters.  The warning-failing constrained module build completes in 2.0 seconds.

The full-fill composition chain now preserves the zero completion flag through the trade result and recursive transition.  `FullTradeUpdate.FullResultAt` records the flag, and `FullStep.fullStepProg_spec` returns it with the existing allocator scratch and owner-tracker facts needed by the next loop iteration.  Warning-failing constrained builds complete `FullTradeUpdate` in 18 seconds, `FullBranch` in 18 seconds, and `FullStep` in 20 seconds.

`FullStep.RecursiveResultAt` groups the complete recursive local frame returned by a full fill, including decremented fuel, carried taker, replacement arrays, owner trackers, and the running flag.  `LoopAdvance.of_full` combines that frame with the physical full-step result, exact source recursion, counter normalization, and one budget expenditure to reconstruct every field of `RunningFacts`.  Warning-failing constrained builds complete the strengthened `FullStep` target in 22 seconds and `LoopAdvance` in 2.4 seconds.

`LoopBranches.partial_spec` connects the dispatcher's quantity frame to the complete partial-fill branch.  It supplies both allocators from `StepBounds` and `RunningFacts`, then converts all four allocator-outcome combinations into the completed invariant through `LoopCompletion.of_partial`.  The warning-failing constrained module build completes in 1.5 seconds.

`LoopBranches.full_spec` connects the same quantity frame to the complete full-fill step.  It supplies the generated preparation frame, both allocator bounds, release-tracker alternatives, and physical invariant facts, then reconstructs `RunningAt` through `LoopAdvance.of_full`.  The warning-failing constrained module build completes in 2.4 seconds.

`LoopIteration.dispatch_spec` composes the generated dispatcher with both branch wrappers and the stopped-state constructor.  `dispatchBranchPost_of_wp` reduces the three nested zero-arity branch continuations to an ordinary suffix for an invariant state, while `LoopCompletion.of_stop` now distinguishes the running input frame from the completion output frame written by `completeProg`.  The warning-failing constrained module build completes in 1.3 seconds after its changed dependencies rebuild successfully.

The loop measure now assigns zero to a completed state and `2 * fuel + 1` to a running state.  Both branch wrappers prove strict decrease: completion reaches zero, and a full fill uses `Budget.fuel_sub_one_toNat` to decrease the running fuel.  `LoopIteration.dispatch_spec` carries that decrease with the invariant through the generated nested continuations, and its warning-failing constrained build completes in 1.2 seconds after all affected modules rebuild in 15 seconds.

`CompletedData` now records the typed fuel local that the generated guard reads before checking the completion flag.  The stopped dispatcher frame and partial-fill result both preserve local 0 explicitly, and the completed constructors retain that fact with the existing output arrays and counters.  Warning-failing constrained builds complete `PartialTradeUpdate` in 9.7 seconds, `PartialBranch` in 10 seconds, `Iteration` in 13 seconds, and the final `LoopIteration` target in 1.2 seconds after its dependencies are current.

`Loop.loopProg_spec` proves the generated zero-arity block and loop from any established `Invariant`.  Completed and zero-fuel running states exit through the guard, while a nonzero running state executes the dispatcher and re-enters with its strict measure decrease.  The warning-failing constrained module build completes in 1.5 seconds.

`LoopInvariant.ExitAt` distinguishes the two states that can leave the generated block: a completed result or a running result with zero fuel.  `Loop.loopProg_spec` now passes that fact to its continuation instead of requiring the continuation to handle every running invariant.  The warning-failing constrained loop build completes in 1.4 seconds after all affected invariant modules rebuild successfully.

`LoopInitial.initialData` names the zero-step running state, and `LoopInitial.of_initial` constructs every `RunningFacts` field from the public input representation and allocator premises.  The constructor proves the initial source equations, counter normalizations, owner trackers, page facts, and complete future allocation budget without elaborating generated instructions.  The warning-failing constrained module build completes in 2.0 seconds.

`LoopResult.OutputAt` gives completed and zero-fuel running exits one public store predicate.  `resultEpilogueProg_spec` proves that the generated epilogue returns the exact source remaining quantity and represented book and trade roots while preserving the free list and expected allocator counters.  The warning-failing constrained module build completes in 1.5 seconds.

The first whole-body comparison exposed flattened control in both allocation-bearing matcher branches.  The generated full-fill path performs the erased-book update inside two nested one-result bounds branches and resumes the trade and release phases after those branches, while the partial-fill path performs the replacement-book update inside one one-result bounds branch and resumes the trade update afterward.  The corrected program definitions preserve these control boundaries, and a closed-data comparison now matches all 85,289 characters of the generated `func14` representation.

`BranchPost` names the one-result and nested two-result continuations, proves their composition from an ordinary suffix proof, and provides a record-update equality that avoids reducing large local frames beneath the irreducible weakest precondition.  `PartialBookPrepare` now proves only the selected-maker read prefix, while `PartialBookControl` proves the four-instruction width calculation and the opaque one-result allocator branch.  This module split reduced a repeated two-minute wall-clock timeout to constrained warning-failing builds of 18 seconds for the prefix and 2.2 seconds for the control module without raising heartbeat or memory limits.

`Entry.func14_decomposition` proves that the generated matcher body is exactly `Initialization.initProg ++ Loop.loopProg ++ LoopControl.resultEpilogueProg`.  `Entry.initialized_loop_locals` proves that the generated public parameter frame reaches the logical initial loop-local predicate after initialization.  Constrained warning-failing builds complete `PartialBranch` in 11 seconds, `Iteration` in 18 seconds, the rebuilt loop stack in 25 seconds, and `Entry` in 1.9 seconds after dependencies are current.

Lean 4.31 does not accept the prior direct-compiler `--wfail` option.  Focused Lake builds continue to use `lake build <target> --wfail`, while direct `lean` diagnostics use `-E warning`; both command forms remain inside the required cgroup, priority, CPU, and timeout wrapper.  A direct compiler check does not refresh imported object files, so dependency changes require a focused Lake build before a downstream direct diagnostic.

## 2026-07-15: Complete `matchFuel` Artifact Theorem

`ClobMatchFuel.Correct.matchFuel_correct` proves termination of generated function 14 and returns the exact `Model.matchFuelL` remaining quantity, book, and trade list for every represented input under the stated allocator and memory budget.  Its postcondition identifies refcount-one result arrays, the represented final free list, exact allocation and release counters, and the unchanged memory-page count.  `Entry.func14_decomposition` ties the theorem to all 85,289 characters of the generated body rather than to a proof-specific approximation of its branch structure.

`MemoryFrame.BytesEqFrom` states byte equality at every address at or above a reserved heap boundary.  Reusable lemmas preserve it across selected-node allocation, bump allocation, flat payload writes, and fixed-array release, while `LoopBounds` proves that both allocation pairs remain below `ctx.limit`.  The running and completed invariants carry the relation from `ctx.initialMem` to the final store, so the public theorem preserves the complete memory region above the budgeted heap range.

Focused warning-failing builds completed `PartialTradeUpdate` in 11 seconds, `PartialBranch` in 11 seconds, `FullTradeUpdate` in 18 seconds, `FullBranch` in 19 seconds, and `FullStep` in 18 seconds.  The rebuilt branch dispatcher completed in 2.4 seconds, the recursive loop in 1.4 seconds, and `Project.ClobMatchFuel.Correct` in 2.1 seconds after its dependencies were current.  Every Lean and Lake command ran serially under the repository cgroup, CPU, scheduler, I/O-priority, and timeout limits.

## 2026-07-15: `matchFuel` Source Properties

`ClobMatchFuel.Properties.MatchStepL` records the exact full-fill and partial-fill source transitions.  `matchFuelL_steps` proves that every recursive result follows the reflexive transitive closure of those transitions.  Each transition appends one trade, while named index lemmas describe the full-fill shift and the partial-fill preservation of every unselected order.

`orderQtyTotal` and `tradeQtyTotal` interpret fixed-width quantities as natural numbers before summing them.  A full step subtracts only after proving that the maker quantity does not exceed the remainder, and a partial step subtracts only after proving the converse ordering.  The resulting step and recursive theorems conserve both maker inventory plus executed trades and taker remainder plus executed trades without an overflow premise.

The focused warning-failing `Project.ClobMatchFuel.Properties` build completed in 1.5 seconds.  The proof uses the existing source branch equations, `findBestL_some_lt`, and small reusable list-total lemmas.  Every Lean invocation ran serially under the repository cgroup, CPU, scheduler, I/O-priority, and timeout limits.

## 2026-07-15: Register the `limit` Artifact

The `clob_limit` case now has checked WASM and WAT inputs plus an emitted `Project.ClobLimit.Program`.  The artifact is 9,330 bytes of WASM and 121,746 bytes of WAT.  Exported function 21 calls `runMatch` at function 18, which calls the recursive matcher at function 17, while functions 22 through 25 implement the shared runtime suite.

`ClobLimit.Model.limitL` composes the existing validity predicate and `matchFuelL` model.  Named equations state the invalid, fully filled, and residual-order branches.  `runMatchL_quantity_conservation` specializes the source matcher theorem to an empty initial trade list and the order's initial quantity.

The constrained generator completed in 7.0 seconds, the focused source-model build completed in 1.2 seconds, and the shared runtime checks completed in 1.2 seconds.  A separate constrained artifact-only run reproduced the checked WASM and WAT byte-for-byte.  The case remains outside `Project.lean`, `tools/check-talos.sh`, and the completed-proof inventory until its input-generic artifact theorem is complete.

## 2026-07-15: Prove `limit` Order Validity

`ClobLimit.ValidOrder` proves the generated side validator, identifier scan, and combined order-validity function for every represented input book.  The seven generated validity functions are definitionally equal to the corresponding `postOnly` functions, and the theorem states the same `validOrderL` result at the `limit` module's function 6.  The focused target itself completed in 8.0 seconds after a 103-second first build of its previously stale `ClobPostOnly.SearchHelpers` dependency.

## 2026-07-15: Prove the Invalid `limit` Branch

`ClobLimit.Invalid.limit_invalid` proves the exported invalid-order branch for every represented input book under an empty free list and a bounded bump allocation.  The theorem returns the borrowed book and a fresh empty trade array, fixes the heap-top and allocation-counter changes, preserves the page count, and frames every byte below the old heap top.  `ClobLimit.Allocation` isolates the two generated status helpers and the shared fixed-array allocation theorem supplies the empty trade-array header; the warning-failing invalid target completed in 18 seconds under the repository resource limits.

## 2026-07-15: Transport the Embedded Search Region

`Project.FunctionRegion` defines a portable subset of the interpreter syntax and a finite function-region renaming relation.  Its semantic theorem proves exact `run` equality at every fuel and transports `TerminatesWith` specifications between modules.  The proof uses the interpreter's `execOne.eq_def` and `execOne_loop_succ` lemmas, which reduce the one-instruction build from repeated multi-minute elaboration to less than one second.

`ClobLimit.SearchRegion.searchShift` certifies the exact six-function mapping from matching functions 2, 5, 6, 7, 8, and 9 to limit functions 8, 10, 11, 12, 13, and 14.  `prove_portable` constructs the closed-syntax certificate while the artifact module discharges its finite call-domain facts.  The Limit loop and wrapper now inherit the owner-aware source specifications without a copied weakest-precondition proof.

Warning-failing constrained builds completed `Project.FunctionRegion.NoTail` in 3.2 seconds, `Project.FunctionRegion.Exec` in 0.40 seconds, and the six-function certificate in 4.3 seconds.  The transported `Project.ClobLimit.FindBest` and `FindBestWrapper` targets completed in 1.9 and 1.5 seconds.  Every Lean and Lake invocation ran serially under the repository cgroup, CPU, scheduler, I/O-priority, and timeout limits.

## 2026-07-15: Prove Internal Matcher Early Exits

`ClobLimit.InternalEarlyExit` proves exact termination of function 17 when its fuel or remaining quantity is zero.  A third theorem covers a nonzero state whose owner-aware embedded search returns no maker.  All three theorems return the unchanged remaining quantity and both owner-and-pointer pairs in generated result order while preserving the complete store.

The proof retains both expanded `Locals.get` hypotheses and exact raw-list facts.  The interpreter guard reductions consume the expanded getter equalities, while the call frame and epilogue calculation use the raw parameter and local equalities.  The no-maker theorem invokes the transported function 14 owner-aware specification instead of repeating the search proof.  Its focused warning-failing build completed in 18 seconds, and the aggregate Limit specification completed in 2.1 seconds under the repository resource limits.

## 2026-07-15: Prove Internal Iteration Control

`ClobLimit.InternalIteration.dispatchProg_spec` proves the non-allocation portion of one function 17 iteration.  It checks the remaining quantity, invokes the transported owner-aware search theorem, reads the selected maker quantity from the represented book, and chooses a caller-supplied full or partial branch.  Its callbacks receive either the complete five-value result frame or the selected index and exact search scratch frame.

The full and partial programs remain theorem parameters, which prevents either allocation body from entering this module's elaboration boundary.  The theorem retains the three nested zero-result branch continuations required by the generated control structure.  Its focused warning-failing build completed in 12 seconds, and the aggregate Limit specification completed in 2.4 seconds under the repository resource limits.

## 2026-07-15: Consolidate Bump Arithmetic

`FixedArrayAllocation` now proves the unsigned normalizations shared by generated bump allocators.  The lemmas cover the data root, metadata offsets, top minus one, required pages, the encoded memory size, and the conclusion that a bounded allocation needs no memory growth.  Their premises state each no-wrap, page-fit, and maximum-page fact explicitly.

The Limit matcher uses three scratch-local layouts across four inline allocations, while earlier CLOB artifacts repeated the same arithmetic in each layout-specific proof.  The shared lemmas leave those adapters responsible only for instruction execution and their final local frame.  The focused warning-failing build completed in 2.3 seconds under the repository resource limits.  The dependent invalid branch and aggregate Limit specification rebuilt in 18 and 1.8 seconds.

`fixedArrayAllocBumpStore` now belongs to `Project.Clob` beside the header transformation that defines its memory.  The shared module also proves its page, global, and fresh-header facts.  `ClobMatchFuel.BookAllocBump` retains its old qualified name as an abbreviation and completed its warning-failing compatibility build in 7.3 seconds.  The dependent Limit invalid branch and aggregate specification rebuilt in 19 and 1.0 seconds.

## 2026-07-15: Prove the Internal Book Bump Allocator

`ClobLimit.InternalBookBump.partialBookBumpProg_spec` proves the generated partial-book bump body after an unsuccessful free-list search.  It covers the heap-top update, page calculation, no-growth branch, six fixed-array header writes, and exact scratch-local result frame.  The semantic result uses the common `fixedArrayAllocBumpStore` with stride five.

`partialBookNoFitProg_spec` adds the generated scratch initialization and complete free-list scan.  Under global 1 equal to zero, the first loop guard exits before any free-node read and composes directly with the bump theorem.  The module still excludes the allocation counter, payload copy, maker replacement, and trade update.

The adapter uses the shared bump arithmetic and store facts while retaining the concrete function 17 indices 69 through 74.  The focused warning-failing build completed in 7.4 seconds, and the aggregate Limit specification completed in 1.2 seconds under the repository resource limits.  Every Lean process used the repository cgroup, CPU, scheduler, I/O-priority, and timeout limits.

## 2026-07-15: Prove the Internal Trade Bump Allocator

`ClobLimit.InternalTradeBump.tradeBumpProg_spec` proves the generated trade bump body after an unsuccessful free-list search.  It covers the heap-top update, page calculation, no-growth branch, six fixed-array header writes, and exact scratch-local result frame.  The semantic result uses the common `fixedArrayAllocBumpStore` with stride four.

`tradeNoFitProg_spec` adds the generated scratch initialization and complete free-list scan.  Under global 1 equal to zero, the first loop guard exits before any free-node read and composes with the bump theorem.  The same instruction sequence and local layout occur in the full- and partial-fill branches, so this theorem covers both trade-allocation sites.

The adapter retains the concrete function 17 indices 68 through 73.  Its scope excludes the allocation counter, payload copy, and appended trade stores, which later branch modules must compose around the allocator.  The focused warning-failing build completed in 7.3 seconds under the repository resource limits.

## 2026-07-15: Prove the Internal Full-Book Allocator

`ClobLimit.InternalFullBookBump.fullBookBumpProg_spec` proves the generated full-fill replacement-book bump body.  It covers the same stride-five store transformation as the partial-book theorem while retaining the full branch's distinct scratch frame.  The result records the heap-top update, page calculation, no-growth branch, six header writes, and final allocator locals.

`fullBookNoFitProg_spec` composes the generated scratch initialization, free-list scan, and bump body when global 1 is zero.  The full-book layout uses instruction locals 66 through 71 and local-list positions 55 through 60.  Together with the partial-book and shared trade adapters, this theorem completes the three numeric allocator layouts in function 17.

The module excludes the allocation counter, erased-book copy, and later trade update.  Those operations require separate semantic postconditions around the allocator result.  The focused warning-failing build completed in 7.5 seconds under the repository resource limits.

## 2026-07-15: Prove Partial-Book Preparation

`ClobLimit.InternalPartialBookPrepare.partialBookPrefixProg_spec` proves the partial-fill prefix through the replacement-book bounds guard.  It reads all five fields of the selected maker from a represented order array and computes the maker quantity after subtracting the taker remainder.  It also reads the source length and retains the generated source, index, field, and scratch locals.

The proof specializes the established `matchFuel` argument to function 17's eleven-parameter, sixty-four-local frame.  The source book and remaining quantity are parameters 7 and 10, while the selected index occupies local-list position 14.  The shared `OrdersAt` lemmas discharge the same field-read and address-bound obligations without adding another memory abstraction.

The module ends before the four instructions that multiply the book length by five and before allocation.  This boundary keeps the generated one-result bounds branch out of the field-read theorem.  The focused warning-failing build completed in 16 seconds under the repository resource limits.

## 2026-07-15: Generalize Branch Continuations

`Project.BranchPost` defines one-result and nested-result branch postconditions for an explicit `Wasm.Module`.  It also proves the true-branch composition and empty-program continuation lemmas once.  `ClobMatchFuel.BranchPost` now provides compatibility specializations with every existing matcher theorem name and statement preserved.

The first completed matcher rebuild exposed stale source proofs from the earlier bump-store move.  `AllocatorFrame` now delegates page and global preservation to `Project.Clob`, and the bump adapters explicitly reduce the common store definition at their final continuation.  Downstream matcher modules qualify the compatibility facts and reduce the common definition when reading unchanged global 2.

Focused warning-failing builds completed the generic branch helper in 2.2 seconds, its matcher specialization in 1.3 seconds, `AllocatorFrame` in 3.6 seconds, both bump adapters in 6.1 and 5.0 seconds, and `Iteration` in 15 seconds.  The complete `Project.ClobMatchFuel.Spec` source rebuild then passed through the recursive loop and public correctness theorem.  Every Lean process ran serially under the repository cgroup, CPU, scheduler, I/O-priority, and timeout limits.

## 2026-07-15: Prove Partial-Book Control

`ClobLimit.InternalPartialBookControl.partialBookSuccessProg_spec` proves the four generated instructions that multiply the represented source length by the order stride and store the flat-word count.  Its update body is a program parameter with an exact prepared local frame.  The theorem therefore excludes every allocation, copy, and replacement instruction from its elaboration boundary.

`partialBookBranchProg_spec` composes the field-read prefix with the generated one-result bounds branch.  It uses `Project.BranchPost.trueOneResultIff` at the Limit module, then passes the opaque update body the shared one-result continuation.  This establishes the control frame required to add the physical replacement-book theorem without re-elaborating the maker reads.

The focused warning-failing module build completed in 2.4 seconds under the repository resource limits.  The proof imports the shared branch helper directly and adds no Limit-specific continuation copy.  Allocation, payload copy, maker replacement, and the later trade update remain open.

## 2026-07-15: Prove Partial-Book Allocator Preparation

`ClobLimit.InternalPartialBookAllocPrepare.partialBookAllocPrepareProg_spec` proves the generated aligned-capacity calculation and free-list scratch initialization.  The theorem identifies the capacity as `fixedArrayBytesU n 5` by using the shared rounding and natural-value lemmas in `Project.Clob`.  Its final state is the exact `InternalBookBump.allocFrame` consumed by the previously proved empty-free-list allocator.

The theorem keeps the two untouched allocator scratch values as premises because the generated prefix does not initialize those locals.  The empty-list scan does not read either value, and the bump body overwrites both before returning.  Keeping them explicit preserves an exact frame without adding an artificial write to the artifact program.

The focused warning-failing build completed in 3.7 seconds under the repository resource limits.  The module contains the generated 27-instruction prefix and no allocation, copy, or maker-store instructions.  The next composition will join this frame to the empty-list bump result and derive the fresh replacement-array facts required by the copy loop.

## 2026-07-15: Compose the Partial-Book Allocator

`ClobLimit.InternalPartialBookAlloc.partialBookAllocProg_spec` composes the aligned-capacity prefix with the complete generated search and bump fallback.  The current Limit theorem assumes global 1 contains zero, so the scan exits before reading a free-node header.  The resulting store is `fixedArrayAllocBumpStore st g0 (fixedArrayBytesU n 5) 5`, and the result local contains `g0 + 48`.

The proof derives the allocator's minimum-capacity premise from the shared `fixedArrayBytesU_toNat` theorem.  It composes `partialBookSearchProg_empty` with `partialBookBumpProg_spec`, passing the existing top, 32-bit fit, memory fit, and page-count premises to the bump theorem.  The first committed definition appended the standalone no-fit program and therefore duplicated its six-instruction search initialization after the setup prefix.  The corrected definition appends the search and bump programs directly, matching the generated slice.

The corrected focused warning-failing build completed in 2.8 seconds under the repository resource limits.  The aggregate rebuild recompiled both downstream partial-book modules and passed the Limit specification.  The composition adds no new arithmetic or memory semantics.

## 2026-07-15: Prove the Partial-Book Copy

`ClobLimit.InternalPartialBookCopy.partialBookCopyProg_spec` proves the generated global-2 increment, target assignment, length initialization, and complete flat-word copy.  Its loop invariant retains the fresh stride-five allocation header, the represented source book, the exact target length, and byte equality outside the target payload.  At loop exit, `OrdersAt.ofFlatWords` reconstructs the represented target book from the copied words.

The module adapts the established structured copy argument to the Limit function's local indices.  It uses the shared `FreshFixedArrayAt.write64_data`, source framing, flat-word separation, and outside-payload write lemmas.  No allocator instructions or selected-maker replacement stores occur in its elaboration boundary.

The focused warning-failing build completed in 5.2 seconds under the repository resource limits.  The proof records the target and cursor at local-list positions 49 and 50 while preserving the allocator result at position 63.  The next theorem will apply the five generated maker-field stores to the represented target book.

## 2026-07-15: Prove Partial-Book Finalization

`ClobLimit.InternalPartialBookFinish.partialBookFinishProg_spec` proves the five generated stores at the selected maker slot and the returned replacement pointer.  The instruction adapter uses maker fields from local-list positions 51 through 55 and the selected index from position 46.  Its final book represents `ClobMatchFuel.Model.setQtyL os i qty`.

The proof reuses `ClobMatchFuel.BookReplaceStore` for the memory transformation.  Those source-independent theorems establish the represented list update and fixed-array header preservation, while the adapter extends the copy theorem's outside-payload frame through each store.  No allocator or copy-loop instruction occurs in this module.

The focused warning-failing build completed in 5.1 seconds under the repository resource limits.  The final local frame contains the replacement pointer as the branch's one result.  The next theorem will compose allocator, copy, and finalization results without reducing any of those instruction bodies.

## 2026-07-15: Compose the Partial-Book Update

`ClobLimit.InternalPartialBookUpdate.partialBookUpdateProg_spec` composes the exact allocator, copy, and finalization programs.  It derives target bounds and source-target separation from the source-capacity and below-heap premises.  The proof invokes each component theorem through its continuation and does not reduce any component instruction body.

The result retains `OwnedOrderArrayAt` for the source book and the replacement book representing `setQtyL os i qty`.  It also provides byte equality outside the target payload from the semantic bump store, unchanged page count from the original store, and the exact global list after counter 2 increases.  `AllocatorFrame.ownedOrderArrayAt_fixedArrayAllocBumpStore` supplies source ownership after allocation, and `OwnedOrderArrayAt.frame_outsideFlatWords` carries it through the copy and maker stores.

The focused warning-failing build completed in 6.8 seconds under the repository resource limits.  The first diagnostic build found only local bound conversions and a missing namespace; the edited theorem passed on the next run.  The following generated segment prepares and appends the partial-fill trade.

## 2026-07-15: Prove Partial-Trade Preparation

`ClobLimit.InternalPartialTradePrepare.partialTradePrepareProg_spec` proves the generated prefix after the replacement-book branch returns.  It consumes the new book pointer, records the old trades, reads the selected maker identifier and price from the old book, and uses the remaining taker quantity as the fill quantity.  It also reads the old trade length and computes both the old flat-word count and appended length.

The theorem adapts the completed `ClobMatchFuel.PartialTradePrepare` argument to the Limit ABI.  Parameters hold the taker identifier, old book, old trades, and remaining quantity, while the selected index remains at local-list position 14.  The final frame places the prepared trade fields and lengths at the exact positions consumed by the stride-four allocator and append loop.

The focused warning-failing build completed in 4.8 seconds under the repository resource limits.  The module ends before the aligned-capacity calculation at generated line 3160.  Trade allocation, payload copy, append stores, and partial-result finalization remain separate proof boundaries.

## 2026-07-15: Prove Partial-Trade Allocator Preparation

`ClobLimit.InternalPartialTradeAllocPrepare.partialTradeAllocPrepareProg_spec` proves the generated stride-four capacity calculation and allocator initialization.  It identifies the capacity as `fixedArrayBytesU n 4` through the shared fixed-array rounding theorems.  Its final state is the exact `InternalTradeBump.allocFrame` consumed by the trade search.

The generated prefix preserves the old capacity and next-node scratch values at local-list positions 60 and 61.  The theorem keeps those values as premises while setting need, predecessor, current node, and result at positions 57, 58, 59, and 62.  This frame states every allocator scratch value without adding instructions to the artifact program.

The focused warning-failing build completed in 2.6 seconds under the repository resource limits.  The module contains the capacity calculation and the sole search initialization.  The next composition will append the search and bump programs directly.

## 2026-07-15: Compose the Partial-Trade Allocator

`ClobLimit.InternalPartialTradeAlloc.partialTradeAllocProg_spec` composes the stride-four setup with the generated search and bump programs.  Global 1 contains zero under the current Limit invariant, so the search exits without reading a free-node header.  The resulting store is `fixedArrayAllocBumpStore st g0 (fixedArrayBytesU n 4) 4`, and the result local contains `g0 + 48`.

The proof derives the minimum-capacity premise through `fixedArrayBytesU_toNat`.  It invokes `tradeSearchProg_empty` and `tradeBumpProg_spec` directly after the setup theorem.  This composition includes the generated search initialization exactly once.

The focused warning-failing build completed in 1.9 seconds under the repository resource limits.  The theorem keeps the capacity and page bounds as explicit premises for later heap-budget composition.  The next module starts from the semantic bump store and copies the old trades before appending the new trade.

## 2026-07-15: Prove the Partial-Trade Copy

`ClobLimit.InternalPartialTradeCopy.partialTradeCopyProg_spec` proves the generated counter increment, target assignment, extended-length store, and complete old-trade prefix copy.  Its invariant retains the source `TradesAt`, fresh stride-four target header, and copied flat-word equality.  The memory frame covers the complete target payload for `ts ++ [trade]`, including the four words that the next module will write.

The adapter uses source, old-word total, new length, and allocator result at local-list positions 45, 47, 48, and 62.  It records target and cursor at positions 49 and 50.  The loop proof reuses the shared trade-word framing and fixed-array header lemmas.

The focused warning-failing build completed in 4.6 seconds under the repository resource limits.  The module contains generated lines 3358 through 3400 and no appended-field stores.  The next proof will identify the four generated stores with the shared append-trade memory transformation.

## 2026-07-15: Prove Partial-Trade Finalization

`ClobLimit.InternalPartialTradeFinish.partialTradeFinishProg_spec` proves the four generated append stores and returned trade-array pointer.  It reads the old length and prepared trade fields from local-list positions 46 and 51 through 54.  The final store represents `ts ++ [trade]`.

The proof reuses `ClobMatchFuel.TradeAppendStore` for the memory transformation.  Those source-independent theorems reconstruct `TradesAt` and preserve the fixed-array header, while the Limit adapter extends the copy theorem's outside-payload frame through each store.  The module contains no allocation or copy-loop instructions.

The focused warning-failing build completed in 5.4 seconds under the repository resource limits.  The final frame returns the new trade pointer as one value.  The following composition will retain both live arrays, exact allocator state, and the semantic appended trade.

## 2026-07-15: Compose the Partial-Trade Update

`ClobLimit.InternalPartialTradeUpdate.partialTradeUpdateProg_spec` composes generated lines 3160 through 3449.  It invokes the allocation, copy, and finalization theorems without unfolding their instruction proofs.  The resulting theorem returns the extended trade array and retains the exact generated frame.

The proof preserves ownership of the old book, replacement book, old trade array, and new trade array.  It also preserves the page count, states the exact allocator globals after the trade counter increment, and carries the allocator-to-final outside-payload memory frame.  Shared allocator-frame theorems preserve each live source array across the bump allocation and subsequent target writes.

The first focused warning-failing build passed in 7.1 seconds under the repository resource limits.  The successful first build confirms that the component boundaries keep this elaboration step small.  The next proof covers generated lines 3450 through 3456, which assign the completed branch result locals.

## 2026-07-15: Prove Partial-Fill Result Assignments

`ClobLimit.InternalPartialFinish.partialFinishProg_spec` proves generated lines 3450 through 3456.  The instructions consume the new trade pointer, store it in local-list positions 2 and 3, and leave an empty operand stack.  They also store zero remaining quantity at position 4 and the completion flag at position 5.

Function 17 has eleven parameters, so combined local indices 13 through 16 correspond to those four local-list positions.  The theorem states the exact resulting frame and leaves the store unchanged.  It requires only the parameter length, local length, and one-value input stack.

The focused warning-failing build completed in 2.3 seconds under the repository resource limits.  This pattern also occurs in `ClobMatchFuel.PartialFinish`, but the local indices and frame shapes differ.  A common parameterized theorem should wait until a third artifact needs the same assignment pattern.

## 2026-07-15: Compose the Partial-Trade Branch

`ClobLimit.InternalPartialTradeBranch.partialTradeBranchProg_spec` composes generated lines 3087 through 3456 after the replacement-book result reaches the operand stack.  It invokes the trade preparation, allocation and update, and result-assignment theorems without unfolding their instruction proofs.  The final frame records equal owner-and-pointer values for both result arrays, zero remaining quantity, and completion.

The theorem preserves the old book, replacement book, old trade array, and appended trade array.  Its other postconditions state the exact page count, allocator globals after the trade counter increment, and allocator-to-final outside-payload memory frame.  The semantic appended value is `ClobMatchFuel.Model.fillTradeL taker maker remaining`.

The focused warning-failing build completed in 5.7 seconds under the repository resource limits.  The first diagnostic pass exposed an omitted ownership namespace and an explicit trade-quantity equality, and the second exposed a frame namespace and parameter-length simplification.  Each diagnostic completed in less than seven seconds, and the successful build retained the intended component boundaries.

## 2026-07-16: Compose the Partial-Fill Branch

`ClobLimit.InternalPartialBranch.partialBranchProg_spec` composes the bounds-checked replacement-book branch with the complete trade continuation.  Its semantic result contains the selected maker with quantity reduced by the taker remainder and one appended `fillTradeL`.  The result locals contain equal owner-and-pointer values for both new arrays, zero remaining quantity, and completion.

The proof preserves ownership of the source book and old trade array across both bump allocations and both payload updates.  It states the final heap pointer, zero free-list head, allocation counter `g2 + 2`, unchanged page count, and byte equality below the original heap top.  The shared bump-allocation and outside-payload frame theorems supply the cross-allocation preservation facts.

The focused warning-failing build passed in 106 seconds under the repository resource limits.  Earlier passes exposed missing namespaces, explicit `List.set` bounds, and a modular-addition goal that required associativity instead of `omega`.  Larger loop proofs must import this theorem opaquely because expanding its dependent frame expressions would repeat that elaboration cost.

## 2026-07-16: Prove Full-Book Preparation

`ClobLimit.InternalFullBookPrepare.fullBookBranchProg_spec` proves the generated full-fill entry through both selected-index bounds checks.  It copies the taker fields, source book, and selected index into the working locals.  Its final frame records the erased length and exact prefix and suffix word counts.

The theorem treats the allocation-and-copy body as an arbitrary program returning one result.  `BranchPost.doubleResultIffPost` accounts for the two nested generated branches without expanding the continuation.  The proof uses the represented source book for both length reads and converts every `UInt64` subtraction and multiplication to the corresponding natural-number range.

The focused warning-failing build completed in 4.3 seconds under the repository resource limits.  The theorem passed on its first build.  The next phase computes the aligned stride-five allocation size and initializes the empty free-list search.

## 2026-07-16: Prove Full-Book Allocator Preparation

`ClobLimit.InternalFullBookAllocPrepare.fullBookAllocPrepareProg_spec` proves the generated aligned-capacity calculation for the erased order array.  It identifies the result as `fixedArrayBytesU n 5` through the shared fixed-array rounding theorems.  The minimum-capacity branch leaves that value unchanged because every fixed-array allocation includes its eight-byte length word.

The theorem initializes predecessor, current node, and allocation result at the exact positions consumed by `InternalFullBookBump`.  It retains the existing capacity and next-node scratch values because the empty-list path does not read them.  The final state is `InternalFullBookBump.allocFrame base (fixedArrayBytesU n 5) 0 g1 capacity next 0`.

The focused warning-failing build completed in 3.6 seconds under the repository resource limits.  The theorem passed on its first build.  The next composition appends the existing empty free-list scan and bump allocator without duplicating either initialization.

## 2026-07-16: Compose the Full-Book Allocator

`ClobLimit.InternalFullBookAlloc.fullBookAllocProg_spec` composes the full-book setup, empty free-list scan, and bump fallback.  Its program contains the search initialization exactly once in the setup prefix.  The resulting store is `fixedArrayAllocBumpStore st g0 (fixedArrayBytesU n 5) 5`.

The proof derives the allocator's eight-byte minimum from `fixedArrayBytesU_toNat`.  It invokes `fullBookSearchProg_empty` and `fullBookBumpProg_spec` after the setup theorem without unfolding their instruction bodies.  The final frame records target `g0 + 48`, the new heap top, and the generated page target.

The focused warning-failing build completed in 2.2 seconds under the repository resource limits.  The theorem passed on its first build.  The next modules prove the replacement-book length store and the prefix and shifted-suffix copy loops.

## 2026-07-16: Prove the Full-Book Prefix Copy

`ClobLimit.InternalFullBookPrefix.fullBookPrefixProg_spec` proves the counter increment, replacement-book length store, and copy loop before the selected maker.  Its invariant retains the fresh stride-five target header and represented source book.  It records equality for every copied flat word and equality outside the complete target payload.

The loop starts from `InternalFullBookBump.allocFrame` and records the target and cursor at local-list positions 51 and 52.  It reads the source, prefix word count, and erased length from positions 45, 48, and 50.  The postcondition provides the prefix fact consumed by `OrdersAt.eraseIdx_ofFlatWords` after the suffix loop.

The first focused build reported that `FreshOrderArrayAt` was a matcher-specific alias absent from this module's namespace.  Replacing it with the shared `FreshFixedArrayAt st target arrayCapacity 5` predicate removed the unnecessary dependency, and the warning-failing build completed in 3.9 seconds.  The next module proves the shifted-suffix copy and reconstructs the represented erased order list.

## 2026-07-16: Prove the Full-Book Suffix Copy

`ClobLimit.InternalFullBookSuffix.fullBookSuffixProg_spec` proves the shifted-suffix loop and returns the replacement-book pointer.  The loop copies source word `prefix + 5 + k` to target word `prefix + k`, skipping the selected five-word maker.  Its invariant retains every completed prefix word while accumulating the shifted-suffix equality.

At loop exit, the theorem applies the shared `OrdersAt.eraseIdx_ofFlatWords` reconstruction lemma.  The result is `OrdersAt st2 target (os.eraseIdx i)` with the original allocation store as the outside-payload frame reference.  The theorem also retains the fresh target header, represented source book, exact counter update, and unchanged page count.

The focused warning-failing build completed in 6.4 seconds under the repository resource limits.  The theorem passed on its first build.  The next module composes the full-book allocator with both copy loops and promotes the represented arrays to owned arrays.

## 2026-07-16: Compose the Full-Book Update

`ClobLimit.InternalFullBookUpdate.fullBookUpdateProg_spec` composes the empty-list allocator with both erased-book copy loops.  It derives target bounds and source-target separation from the source-capacity and below-heap premises.  The continuation receives owned source and replacement books, the allocation-to-final outside-payload frame, unchanged pages, and the exact global-list update.

The proof keeps all component instruction theorems opaque.  It uses `ownedOrderArrayAt_fixedArrayAllocBumpStore` to preserve the source through allocation and `OwnedOrderArrayAt.frame_outsideFlatWords` to preserve it through both loops.  The target ownership pairs the allocator's fresh stride-five header with the suffix theorem's `OrdersAt st2 target (os.eraseIdx i)` result.

The first diagnostic found an implicit byte conversion and incorrectly aligned continuation bullets, and the second found two explicit natural-byte identities and a result frame that wrapped the allocator frame twice.  The corrected warning-failing build completed in 3.9 seconds under the repository resource limits.  The next generated segment prepares the maker trade and the stride-four append allocation.

## 2026-07-16: Prove Full-Trade Preparation

`ClobLimit.InternalFullTradePrepare.fullTradePrepareProg_spec` proves the generated bridge after the erased-book branch returns.  It records the replacement book, retains the old trade-array pointer, and reads the matched maker identifier, price, and full quantity from the source book.  It also computes the old flat-word count and appended trade length.

The final local frame matches the input of `InternalPartialTradeUpdate`.  The full-fill and partial-fill branches differ only in the prepared quantity at position 54, so the stride-four allocation, copy, and append-store theorem needs no duplicate.  The replacement book remains in positions 25 and 26 for the later recursive transition.

The focused warning-failing build completed in 5.9 seconds under the repository resource limits.  The theorem passed on its first build.  The next composition reuses the shared trade update with quantity `os[i]!.oqty`.

## 2026-07-16: Prove Full-Trade Finalization

`ClobLimit.InternalFullTradeFinish.fullTradeFinishProg_spec` proves generated lines 2560 through 2589.  It records equal owner-and-pointer values for the new trade array and reads the selected maker quantity from the source book.  The final frame contains `remaining - os[i]!.oqty` at local-list position 29.

The theorem leaves memory and globals unchanged.  It ends before the generated release block and recursive-state assignments.  The source book and selected index remain available through parameter positions 7 and local-list position 14 while the instruction scratch values use positions 45 and 46.

The first focused build exposed a local-index translation copied from the nine-parameter matcher frame.  Correcting the scratch positions from 57 and 58 to 45 and 46 produced a warning-failing build in 2.2 seconds under the repository resource limits.  The next module composes full-trade preparation, the shared trade update, and this finalization theorem.

## 2026-07-16: Compose the Full-Trade Update

`ClobLimit.InternalFullTradeUpdate.fullTradeUpdateProg_spec` composes the full-trade preparation, shared trade-array update, and full-trade finalization programs.  The appended value is `ClobMatchFuel.Model.fillTradeL taker oldOrders[i]! oldOrders[i]!.oqty`.  The resulting locals contain the replacement book, appended trade array, and `remaining - oldOrders[i]!.oqty`.

The proof reuses `InternalPartialTradeUpdate.partialTradeUpdateProg_spec` without unfolding its allocator, copy loop, or append stores.  Its continuation retains ownership of the source and replacement books and the source and appended trade arrays.  It also states the allocator-to-final outside-payload frame, unchanged page count, and exact globals after the trade-allocation counter increment.

The first focused diagnostic completed in 4.8 seconds and exposed a missing allocator-frame namespace plus continuation bullets aligned at the wrong proof level.  Correcting those structural errors produced a warning-failing build in 5.1 seconds under the repository resource limits.  The next proof boundary assigns the full-fill result to the recursive-state parameters and decrements the fuel parameter.

## 2026-07-16: Prove the Full-Fill Transition

`ClobLimit.InternalFullTransition.fullTransitionProg_spec` proves generated lines 2590 through 2633.  The program copies the taker and full-fill result through ten scratch locals before assigning parameters 1 through 10.  Its final instruction decrements the fuel in parameter 0.

The result frame states the exact scratch locals and recursive parameters.  The new book and trade owner-and-pointer pairs remain equal, and the reduced remaining quantity becomes parameter 10.  The frame leaves memory and globals unchanged.

`ClobMatchFuel.FullTransition` supplied the proof pattern, but its nine-parameter ABI and conditional owner-tracker calculation differ from the Limit program.  A common theorem would need program indices and tracker behavior as parameters while saving one short direct proof.  The Limit-specific warning-failing build passed on its first run in 1.6 seconds under the repository resource limits.

## 2026-07-16: Compose Full-Fill Book and Trade Updates

`ClobLimit.InternalFullBookTrade.fullBookTradeProg_spec` composes the nested full-book branch with the complete full-trade update.  Its semantic result contains `os.eraseIdx i` and one appended trade for the erased maker's complete quantity.  The theorem retains ownership of the source book, replacement book, old trades, and appended trades.

The proof states the final heap pointer, zero free-list head, allocation counter `g2 + 2`, unchanged page count, and byte equality below the original heap top.  It preserves the old trade array across the book allocation through `ownedTradeArrayAt_fixedArrayAllocBumpStore` and `OwnedTradeArrayAt.frame_outsideFlatWords`.  The generated two-level result branch uses `BranchPost.doubleResultIffPost_of_wp` before the trade update.

Three focused diagnostics completed in 5.4, 4.6, and 4.0 seconds.  They identified an explicit no-wrap comparison, the prepared frame's local-list length, and one unused simplifier argument.  The corrected warning-failing build completed in 4.9 seconds under the repository resource limits, and the recursive transition remains a separate compiled boundary.

## 2026-07-16: Strengthen the Full-Trade Result Frame

The first transition composition review found that `FullTradeResultAt` omitted the unchanged fuel and taker fields read by `fullTransitionProg`.  The concrete frame preserved those values, but the theorem interface did not expose them.  The predicate now states fuel at index 0, the five taker fields at indices 26 through 30, and the replacement state at indices 36 through 40.

`fullTradeUpdateProg_spec` accepts the six preserved input facts and returns them with the semantic array result.  It converts optional `Locals.get` facts to list-element equalities once before simplifying the final frame.  `fullBookTradeProg_spec` supplies the taker facts from `fullBookPrepareFrame`, where the generated full-fill branch copied them before allocation.

The first focused diagnostic completed in 5.0 seconds and identified the optional-access conversion.  The corrected trade-update build completed in 6.1 seconds, and the dependent book-and-trade build completed in 5.1 seconds under the repository resource limits.  The strengthened boundary now contains every premise required by the separately compiled transition theorem.

## 2026-07-16: Compose the Complete Full-Fill Branch

`ClobLimit.InternalFullBranch.fullBranchProg_spec` composes the book-and-trade update with the recursive transition.  Its semantic state contains `os.eraseIdx i`, the appended complete-maker trade, and `remaining - os[i]!.oqty`.  The transition writes equal owner-and-pointer parameters for both replacement arrays and decrements fuel.

`InternalFullBranch.RecursiveResultAt` states the exact eleven recursive parameters, local-list length, and empty operand stack.  `recursiveResultAt_fullTransitionFrame` proves that the explicit transition frame satisfies this predicate from only the input frame lengths.  The branch continuation also retains both source arrays, both replacement arrays, exact allocator globals, unchanged pages, and byte equality below the original heap top.

The focused warning-failing build passed on its first run in 4.3 seconds under the repository resource limits.  The proof invokes the separately compiled book-and-trade and transition theorems without unfolding either instruction sequence.  The next composition connects both allocation-bearing branch theorems to the iteration dispatcher and loop invariant.

## 2026-07-16: Prove Internal Loop Control

`ClobLimit.InternalLoopControl` proves the generated outer guard for a completed state, zero fuel, and a running state.  Fuel resides at parameter 0, while the completion flag resides at combined index 16.  Each theorem preserves the store and exact local frame.

The result epilogue selects parameters 6 through 10 when the loop exits without a completed branch.  A completed state already occupies local-list positions 0 through 4, with its flag at position 5.  Both paths return the five owner-and-pointer values in the generated operand-stack order.

The first focused diagnostic completed in 2.8 seconds and exposed the missing direct import of `InternalIteration`.  The second diagnostic completed in 2.3 seconds and identified two malformed multiline tactic target lists.  Correcting those local errors produced a warning-failing build in 3.8 seconds under the repository resource limits.

## 2026-07-16: Define the Internal Loop Invariant

`ClobLimit.InternalLoopInvariant` defines running, completed, and exit states for function 17.  A running state records the exact recursive parameters, allocation scratch values, residual source computation, represented arrays, and allocator globals.  A completed state records the semantic result and the five owner-and-pointer values consumed by the epilogue.

The invariant omits free-list nodes and release counters because the proved Limit path keeps global 1 equal to zero and uses bump allocation.  It retains global 0, global 2, page count, heap monotonicity, and equality below the initial heap top.  Its budget reuses `ClobMatchFuel.Budget.stepBytes`, which already bounds one replacement book and one appended trade array.

The measure is zero for a completed state and `2 * fuel.toNat + 1` for a running state.  The first focused diagnostic completed in 2.3 seconds and found one incorrect conjunction projection in the completed-value lemma.  Correcting that projection produced a warning-failing build in 2.0 seconds under the repository resource limits.

## 2026-07-16: Derive Internal Loop Step Bounds

`ClobLimit.InternalLoopBounds.StepBounds` collects the numeric premises consumed by both allocation-bearing branch theorems.  It covers source lengths, flat-word totals, aligned allocation sizes, exact `UInt64.toNat` allocation tops, 32-bit address limits, and page fits.  It also bounds each complete two-allocation branch by the invariant's fixed step budget.

`InternalLoopBounds.of_running` derives the record from a nonzero-fuel `RunningFacts`.  It reuses `ClobMatchFuel.Budget.one_step_available`, `allocationTop_toNat`, `fullStepBytes_le`, and `partialStepBytes_le`.  The theorem keeps all modular arithmetic outside the later dispatcher and state-constructor proofs.

The first focused diagnostic completed in 1.5 seconds and found one malformed multiline `change ... at` command.  Moving the target onto the command line allowed the complete warning-failing build to pass in 2.7 seconds under the repository resource limits.  No generalized bound record was added because the existing matcher and Limit invariants have different data types and no third consumer currently repeats the adapter.

## 2026-07-16: Prove Internal Loop Source Progress

`ClobLimit.InternalLoopProgress` relates each dispatcher outcome to the residual `matchFuelL` computation stored in the invariant.  A stopped state equals the current source state, and a partial fill equals its completed source state.  A full fill exposes the recursive source computation at decremented fuel over the erased book and appended trade.

The module defines the semantic full and partial step states once for later invariant constructors.  Its counter lemmas derive the current or post-append expected global 2 from the invariant's trade length and step count.  These theorems keep source unfolding and modular counter arithmetic out of the physical branch compositions.

The focused warning-failing build passed on its first run in 1.5 seconds under the repository resource limits.  The proof reuses the source recurrence and fuel-decrement theorems from `ClobMatchFuel.Model` and `ClobMatchFuel.Budget`.  Completed-state and next-running-state construction remain separate proof boundaries.

## 2026-07-16: Strengthen the Partial-Fill Result Frame

`ClobLimit.InternalPartialTradeBranch.PartialResultAt` now records the unchanged fuel at parameter 0.  The completed loop invariant requires that fact independently of the five semantic result values.  The corresponding `ClobMatchFuel` result predicate already uses the same interface.

`partialTradeBranchProg_spec` accepts the input fuel fact and converts its optional parameter access to an element equality before simplifying the final frame.  `partialBranchProg_spec` preserves the fact through the preceding book allocation and supplies it to the trade continuation.  Neither program definition nor instruction theorem changed.

The focused trade-branch build completed in 5.5 seconds, and the composed partial-branch build completed in 102 seconds under the repository resource limits.  Both warning-failing builds passed.  The next module constructs completed invariant states for stopped and partial-fill iterations.

## 2026-07-16: Construct Completed Internal Loop States

`ClobLimit.InternalLoopCompletion.of_stop` turns a stopped running state into the completed invariant.  It identifies the source result with the current state and retains both owner-and-pointer pairs, array ownership, fuel, pages, heap pointer, and zero free-list head.  Its counter proof derives the expected global 2 from the unchanged trade length.

`InternalLoopCompletion.of_partial` consumes the physical partial-branch result and both replacement arrays.  It identifies the source result with `partialState`, records equal owner-and-pointer values for each replacement array, and derives the expected counter after one appended trade.  Byte equality below the current heap top composes with the running invariant's equality below the initial heap top.

The first focused diagnostic completed in 1.6 seconds and found the missing namespace for the owned-array predicates.  Adding `ClobMatchFuel.AllocatorFrame` allowed the warning-failing build to pass in 1.5 seconds under the repository resource limits.  The next proof boundary constructs the next running state after a full fill.

## 2026-07-16: Retain Internal Allocator Scratch Locals

The running invariant requires four allocator scratch locals with `i64` values at positions 58, 59, 61, and 62.  The complete full-fill theorem previously returned the recursive parameters but omitted those local facts.  That interface could not establish the next `LoopLocalsAt` state.

`InternalIteration.AllocScratchAt` now defines the shared local predicate at the iteration ABI boundary.  `FullTradeResultAt` proves it from the concrete trade-allocation frame, and `RecursiveResultAt` preserves it through `fullTransitionFrame`.  `InternalLoopInvariant` consumes the same predicate directly.

The focused iteration, trade-update, book-and-trade, full-branch, and dependent completion builds all passed with warnings treated as errors.  Their final theorem times ranged from 1.3 to 6.4 seconds under the repository resource limits.  The next-running constructor can now recover every local premise from `RecursiveResultAt`.

## 2026-07-16: Retain the Full-Fill Running Flag

The next-running review found that `RecursiveResultAt` omitted the zero completion flag at combined local index 16.  The full-fill program preserves that flag while updating the recursive parameters.  Without the fact, the successor constructor could not establish the complete `LoopLocalsAt` predicate.

`FullTradeResultAt` now carries the flag through the allocation and append frames.  `fullBookTradeProg_spec` supplies the original running fact across the book frames, and `recursiveResultAt_fullTransitionFrame` preserves it through the parameter transition.  The resulting recursive predicate contains every local fact consumed by the running invariant.

The trade-update, book-and-trade, and full-branch warning-failing builds completed in 6.9, 5.2, and 3.4 seconds under the repository resource limits.  One diagnostic identified the need to unfold `fullBookPrepareLocals` when transporting the combined local access.  The next proof boundary is confined to source progress, lengths, heap bounds, counters, memory equality, and the remaining allocation budget.

## 2026-07-16: Construct the Next Internal Running State

`ClobLimit.InternalLoopAdvance.nextData` defines the state after a complete maker fill.  It increments the step count, decrements fuel, installs equal owner-and-pointer values for both replacement arrays, erases the selected maker, appends its trade, and advances global 2 by two.  `InternalLoopAdvance.of_full` proves `RunningFacts` for that data from the physical branch result.

The constructor combines `full_source` with the exact recursive locals and represented replacement arrays.  It proves the new source and length equations, fuel accounting, allocation counter, heap monotonicity, below-initial-heap memory equality, page and address limits, and the remaining fixed-step budget.  The physical pointer, capacity, heap lower bound, and heap upper bound remain explicit premises for the later branch composition.

The first focused diagnostic completed in 1.7 seconds and found that the trade-limit arithmetic had not introduced `facts.fuelSpent`.  Adding that named equality allowed the warning-failing build to pass in 1.7 seconds under the repository resource limits.  The next module composes the physical partial and full branches with the completion and advancement constructors.

## 2026-07-16: Compose Internal Loop Branches

`ClobLimit.InternalLoopBranches.partial_spec` connects the selected-maker frame to `InternalPartialBranch.partialBranchProg_spec`.  It supplies every allocation premise from `StepBounds` and every represented input from `RunningFacts`.  The physical result feeds `InternalLoopCompletion.of_partial`, and the completed measure is zero.

`InternalLoopBranches.full_spec` connects the same selected-maker frame to `InternalFullBranch.fullBranchProg_spec`.  It derives exact natural values for the fresh book root, fresh trade root, and final heap top, then proves the replacement array bounds and heap-growth premises consumed by `InternalLoopAdvance.of_full`.  The successor measure decreases because the branch decrements nonzero fuel.

The partial-only module first passed in 1.7 seconds.  Three focused diagnostics on the full theorem identified the byte-bound margin, two structure projections needed by no-wrap arithmetic, and the need to unfold `nextData` before measure normalization.  The complete warning-failing build passed in 1.9 seconds under the repository resource limits, and the next boundary composes these paths with the iteration dispatcher.

## 2026-07-16: Compose the Internal Loop Dispatcher

`ClobLimit.InternalLoopIteration.dispatchBranchPost_of_wp` reduces the generated dispatcher's three nested zero-arity branch posts to an ordinary suffix when the local operand stack is empty.  The lemma matches the generated continuation structure without unfolding either allocation branch.  Completed and running invariant values supply its empty-stack premise.

`InternalLoopIteration.dispatch_spec` derives `StepBounds` once from the nonzero-fuel running invariant.  Zero remaining quantity and missing-maker outcomes feed `InternalLoopCompletion.of_stop`, while selected-maker outcomes use `InternalLoopBranches.full_spec` or `partial_spec`.  Each continuation returns the invariant and preserves the strict measure decrease proved by the lower layer.

The focused warning-failing build passed on its first run in 1.3 seconds under the repository resource limits.  The theorem contains no new address or allocator arithmetic.  The next boundary proves the generated guard-dispatch loop by well-founded induction on the established measure.

## 2026-07-16: Prove the Generated Internal Match Loop

`ClobLimit.InternalLoop.bodyProg` is the exact guard, dispatcher, and trailing re-entry branch used by the recursive matcher.  `loopProg` places that body in the generated zero-arity loop and enclosing zero-arity block.  The definitions retain the full and partial branch programs as opaque components.

`InternalLoop.loopProg_spec` applies the interpreter's well-founded loop rule with `Invariant` and `measure`.  A completed state exits through the done guard, a zero-fuel running state exits through the fuel guard, and a nonzero-fuel running state invokes `InternalLoopIteration.dispatch_spec`.  The theorem returns `ExitAt` after the enclosing block exits.

The focused warning-failing build passed on its first run in 1.7 seconds under the repository resource limits.  Neither the dispatcher nor either allocation branch was unfolded.  The next boundary constructs the initial running invariant from function 17's public input frame and allocator premises.

## 2026-07-16: Construct the Initial Internal Running State

`ClobLimit.InternalLoopInitial.initialData` records function 17's starting owners, pointers, capacities, fuel, remaining quantity, heap pointer, allocation counter, book, and trades.  Its step count is zero, so the residual source computation is the context result by definition.  The initial trade-length and allocation-counter equations reduce directly.

`InternalLoopInitial.of_initial` constructs `RunningFacts` from an initialized `LoopLocalsAt` frame and explicit physical premises.  It retains both represented arrays, zero free-list head, globals 0 and 2, heap monotonicity, memory equality below the initial heap top, page facts, address bounds, and the full fuel budget.  The theorem leaves the concrete function-local calculation to the entry module.

The focused warning-failing build passed on its first run in 1.8 seconds under the repository resource limits.  The constructor contains no instruction execution or address arithmetic.  The next boundary unifies completed and zero-fuel exits and proves the generated five-value result epilogue.

## 2026-07-16: Prove the Internal Loop Result

`ClobLimit.InternalLoopResult.OutputData` records both owner-and-pointer pairs, array capacities, and the final heap pointer.  `OutputAt` states ownership of the source result arrays, memory equality below the initial heap top, unchanged pages, zero free-list head, and exact globals 0 and 2.  `outputValues` matches function 17's five-value stack order.

`of_completed` projects the output predicate from `CompletedFacts`.  `of_zero_running` reduces the residual source computation at zero fuel, transports both represented arrays to the context result, and derives the expected allocation counter from the unchanged final trade length.  `resultEpilogueProg_spec` applies the generated completed or running epilogue theorem and returns the same output predicate for both exit forms.

The first focused run found two malformed multiline `simp only ... at` commands before elaboration.  Joining each command with its target allowed the warning-failing build to pass in 1.5 seconds under the repository resource limits.  The next boundary proves function 17's initialization, body decomposition, and complete internal matcher theorem.

## 2026-07-16: Prove the Internal Matcher Entry Frame

`ClobLimit.InternalInitialization.initProg` contains function 17's two initialization instructions, which set the completion flag to zero.  `initProg_spec` proves the exact resulting local frame while preserving the store and all parameters.  Its focused warning-failing build passed in 1.3 seconds under the repository resource limits.

`ClobLimit.InternalEntry.func17_decomposition` proves that the generated function body equals initialization followed by the verified loop and result epilogue.  `initialized_loop_locals` reduces the concrete `func17Def.toLocals` frame to `LoopLocalsAt` for `initialData`, including the zero-initialized allocator scratch locals.  The decomposition and frame theorem remain independent of physical memory premises.

The first entry build left one existential zero-value witness after all finite-list reductions.  Supplying the `UInt64` value zero allowed the warning-failing build to pass in 1.3 seconds under the repository resource limits.  The next theorem composes these boundaries into input-generic termination and correctness for function 17.

## 2026-07-16: Prove the Complete Internal Matcher

`ClobLimit.InternalCorrect.InternalMatchSpec` states input-generic correctness for function 17.  Its premises cover both owner-and-pointer pairs, array capacities and ownership, initial heap and memory identities, allocator globals, pages, address bounds, and the fixed fuel budget.  Its postcondition is the common five-value `InternalLoopResult.Postcondition`.

`InternalCorrect.func17_correct` composes the exact entry decomposition, completion-flag initialization, initial running invariant, terminating loop, and result epilogue.  It proves that the returned remaining quantity and represented arrays equal `ClobMatchFuel.Model.matchFuelL`, while retaining the final heap pointer, zero free-list head, allocation counter, page count, and below-initial-heap memory frame.  No physical branch or loop body is unfolded in the final theorem.

The first focused build reached the final postcondition and left only the length of the named eleven-element `internalArgs` list.  Adding that definition to the final simplification allowed the warning-failing build to pass in 1.7 seconds under the repository resource limits.  Function 18, `runMatch`, is the next proof boundary before the exported Limit branches.

## 2026-07-16: Prove the Repeated `runMatch` Allocation

`ClobLimit.RunMatchEmptyAlloc.allocProg` names the empty stride-four fixed-array allocation that function 18 executes twice.  `allocProg_spec` proves the complete empty-free-list path for an arbitrary compatible function 18 local frame.  Its result contains the zero-length array header, final scratch locals, unchanged page count, heap top `g0 + 56`, and allocation counter `g2 + 1`.

The theorem treats the generated free-list loop and six header stores as one compiled boundary.  It accepts a continuation over the exact resulting store and frame, so the second allocation can consume the first allocation's result without unfolding either instruction block.  The proof uses the existing fixed-array arithmetic lemmas for the no-wrap, no-grow, address, and page obligations.

`ClobLimit.RunMatchEntry.func18_decomposition` identifies both generated allocation regions with `allocProg`.  The allocation theorem passed its focused warning-failing build in 8.8 seconds, and the decomposition passed in 1.2 seconds under the repository resource limits.  The next theorem will prove the function 18 preparation frame, compose both allocations, and call `InternalCorrect.func17_correct`.

## 2026-07-16: Compose `runMatch` Initialization

`ClobLimit.RunMatchPrepare.prepareProg_spec` reads the represented book length and sets function 17's initial fuel to `UInt64.ofNat (os.length + 1)`.  It proves the generated overflow branch unreachable from the 32-bit book-length premise.  The final frame records all taker fields and the book owner-and-pointer pair without changing the store.

`ClobLimit.RunMatchAllocations.allocationsProg_spec` composes both empty-array allocations and the generated owner and data-root assignments.  Two small generic assignment theorems prevent the proof from normalizing the complete 35-local frame while applying the second allocator.  The final instruction frame contains owner root `g0 + 48`, data root `g0 + 104`, remaining quantity `taker.oqty`, and heap top `g0 + 112`.

`allocationsStore_facts` proves that both empty roots remain owned, the input book remains owned, global 1 remains zero, global 2 advances by two, pages remain unchanged, and bytes below the original heap top remain equal.  The preparation build passed in 2.4 seconds, and the complete allocation module passed in 3.1 seconds under the repository resource limits.  The next theorem will apply `InternalCorrect.func17_correct` to this state and prove function 18's result epilogue.

## 2026-07-16: Prove Complete `runMatch`

`ClobLimit.RunMatchCall.CallLocalsAt` states the eleven values consumed by function 17 at the function 18 call site.  `callProg_spec` applies any matching function 17 termination theorem without unfolding its body.  The concrete final allocation frame supplies fuel, taker fields, both book values, both trade values, and the initial remaining quantity.

`ClobLimit.RunMatchResult.resultProg_spec` proves that the generated result epilogue returns function 17's five values unchanged after copying them through locals.  Its interface accepts the source frame and returned values separately, avoiding elaboration of a large record update at the caller.  The focused warning-failing call and result builds completed in 2.7 and 1.2 seconds under the repository resource limits.

`ClobLimit.RunMatchCorrect.func18_correct` composes preparation, both empty-array allocations, function 17, and the result epilogue.  `runMatchContext_result` identifies its source result with `Model.runMatchL`, while the physical postcondition retains represented result arrays, allocator globals, pages, and the post-initialization memory frame.  The focused warning-failing build completed in 1.8 seconds under the repository resource limits, and exported function 21's valid branches are the next proof boundary.

## 2026-07-16: Divide the Exported `limit` Control

`ClobLimit.LimitEntry.func21_decomposition` separates function 21 into its validity prefix, valid branch, invalid branch, and result epilogue.  The valid branch has a second exact division between its function 18 prefix and its filled and residual results.  The large residual and invalid instruction lists remain opaque unless a proof selects them.

The decomposition derives both large lists from their exact positions in the generated function and verifies the complete reconstruction by definitional equality.  Later branch proofs can execute calls and scalar tests without elaborating either allocation body.  The focused warning-failing build passed in 1.3 seconds under the repository resource limits.

## 2026-07-16: Prove the Exported Filled Branch

`ClobLimit.LimitValidEntry.entryProg_valid_spec` executes the parameter copies and validity call against an abstract continuation.  It returns the exact 53-local frame with the valid condition on the operand stack.  Its focused warning-failing build passed in 1.5 seconds under the repository resource limits.

`ClobLimit.LimitRunMatchCall.validCallProg_spec` prepares function 18's seven arguments and applies an arbitrary function 18 theorem without reducing its continuation.  `LimitRunMatchResult` divides the returned-value handling into a pure store phase and a two-condition normalization phase.  The call and result modules passed their focused warning-failing builds in 1.2 and 1.4 seconds under the repository resource limits.

The initial combined proof reached the default heartbeat limit at the validity call, and the first call split moved that limit to result-condition normalization.  Dividing at both generated call boundaries and between result storage and condition testing removed those reductions rather than increasing the heartbeat allowance.  `ClobLimit.LimitFilled.func21_filled` now proves the complete valid zero-remaining branch in 4.2 seconds, returning status zero and the exact owned arrays from `Model.runMatchL` without a further allocation.

## 2026-07-16: Prepare the Exported Residual Branch

The residual append requires the final matcher heap pointer to remain below the context limit.  `InternalLoopInvariant.CompletedFacts` and `InternalLoopResult.OutputAt` now retain that heap bound together with the page, address, and memory limits.  The stopped, partial-fill, completed, and zero-fuel constructors preserve or derive all four facts.

`ClobLimit.LimitEntry` divides the residual path into status, order-field, represented-length, allocator-preparation, allocation, copy, and finish regions.  `LimitResidualStatus.residualStatusProg_spec` proves the status-zero call and matched-book pointer copy.  `LimitRunMatchResult` supplies the residual condition theorem needed to enter that region.

The first preparation proof combined field copies, the length read, and arithmetic over one explicit 53-local frame, reaching the default heartbeat limit.  Dividing it into a field predicate and a generic represented-length phase reduced the warning-failing build to 2.5 seconds under the repository resource limits.  `Project.ClobLimit.InternalCorrect` also rebuilt after the stronger result predicate, so the next phase can derive the residual allocation premises from proved output facts.

`LimitResidualAllocPrepare.residualAllocPrepareProg_spec` computes `orderArrayBytesU (book.length + 1)`, proves that the generated minimum-capacity branch is false, and initializes the allocator locals from global 1.  Its `AllocLocalsAt` predicate retains the prepared order and exposes only the four scratch values required by the empty-list allocator path.  The focused warning-failing build passed in 1.8 seconds under the repository resource limits.

## 2026-07-16: Prove the Residual Book Allocation

`InternalLoopInvariant.CompletedFacts` and `InternalLoopResult.OutputAt` now retain the capacity and separation bounds for both represented result arrays.  The stopped and zero-fuel outcomes inherit the running invariant's bounds, while the partial-fill branch derives exact bounds for both replacement allocations.  These facts allow the exported residual append to preserve the matcher-produced book and trades across a fresh bump allocation.

`ClobLimit.LimitEntry` now names the residual allocator's search body, enclosing loop, bump fallback, and finish instructions.  `LimitResidualBump` proves that the zero free-list head exits the search on its first check and that the fallback writes the shared stride-five fixed-array header.  `LimitResidualAlloc.residualAllocProg_spec` composes those proofs with the global-2 increment, appended-length store, and zero copy counter, returning one semantic allocation store and an exact copy frame.

The focused warning-failing bump and complete-allocation builds passed in 5.8 and 2.7 seconds under the repository resource limits.  The aggregate `Project.ClobLimit.Spec` build passed 3,109 targets in 6.2 seconds under the same limits.  The next boundary proves the residual flat-word copy loop before the five appended-order stores reconstruct the represented book.

## 2026-07-16: Prove the Residual Book Copy

The first combined copy theorem reached its 120-second constrained timeout without a diagnostic.  The proof was not rerun unchanged.  `LimitResidualCopyInvariant.CopyState.advance` now isolates one semantic target write, preserving the fresh header, source book, outside-payload memory, and copied prefix in a separately compiled module.

`LimitResidualCopy.residualCopyProg_spec` handles only the generated block, loop guard, memory guards, and decreasing word counter.  `LimitResidualAllocFacts` states the allocator result's pages, globals, fresh header, stored length, below-heap frame, and preservation of both matcher arrays.  The copy initializer and `LimitResidualAllocCopy.residualAllocCopyProg_spec` use those facts to compose allocation and copying without an assumed initial invariant.

The semantic transition, control theorem, allocator facts, initializer, and allocation-copy composition pass focused warning-failing builds in 1.4, 2.3, 1.4, 1.4, and 1.4 seconds under the repository resource limits.  The composition derives the copy count, target address and page bounds, and source separation from the allocation premises and retained matcher bounds.  The five appended-order stores are the next proof boundary.

## 2026-07-16: Finish the Residual Book

`ClobLimit.LimitEntry` now names the five appended-order stores and the six final result assignments separately.  `LimitResidualFinishFacts.finish` reuses `ClobPostOnly.AppendStore` to reconstruct `book ++ [{ order with oqty := remaining }]`.  Its postcondition retains the fresh header, exact allocator pages and globals, and memory equality outside the new payload.

`LimitResidualCopyInvariant.CopyInvariant.at_end` recovers the completed semantic state from the existential loop invariant and exact counter frame.  `LimitResidualFinish.residualFinishProg_spec` executes every guarded store and assigns status zero, the new book pointer, and the unchanged trades pointer.  The continuation receives both the owned appended book and an exact 53-local result frame.

The explicit residual-program decomposition, semantic finalization, completed-invariant eliminator, and final instruction theorem pass focused warning-failing builds in 1.7, 2.4, 1.5, and 3.4 seconds under the repository resource limits.  Both finalization theorems pass at the default heartbeat limit.  The next boundary completes the input-generic residual branch and composes the exported function.

## 2026-07-16: Compose the Residual Book Program

`LimitResidualBounds.Facts` collects the normalized allocation size, copy count, target address, page fit, and source separation used by allocation, copying, and finalization.  Its derivation passed a focused warning-failing build in 3.2 seconds, and the existing allocation-copy theorem now consumes those shared facts.  This removes a duplicate arithmetic proof from the next composition boundary.

`LimitResidualBook.residualBookProg_spec` composes allocation, flat-word copying, five appended-order stores, and result-local assignments.  Its continuation receives the represented appended book and the exact status, book, and trades locals.  The focused warning-failing build passed in 1.2 seconds under the repository resource limits.

## 2026-07-16: Prove the Valid Residual Branch

`InternalLoopResult.OutputAt` now retains the heap-monotonicity fact already carried by the running invariant.  The stopped, partial-fill, completed, and zero-fuel paths preserve it, which permits the final memory proof to connect the matcher frame with the caller's original heap boundary.  The focused dependency chain through `InternalLoopResult` rebuilt under the repository resource limits.

`LimitResidualResult` preserves the matcher trade array, pages, globals, and below-heap bytes through the appended-book writes.  `LimitResidualExport` then composes the matcher's initial-allocation memory frame and states the owned arrays, exact allocator globals, unchanged pages, and bytes below the caller's original heap top.  Their focused warning-failing builds passed in 1.2 and 2.9 seconds.

`LimitResidual.func21_residual` composes the complete matcher, residual condition, residual allocation and append, and three-result epilogue.  A public reserve premise covers the one final stride-five allocation above the matcher heap limit, from which the proof derives every address and page bound.  The theorem passed a focused warning-failing build in 3.2 seconds, and the complete three-branch exported theorem is the next boundary.

## 2026-07-16: Complete the Exported `limit` Theorem

`LimitCorrect.func21_correct` splits on order validity and the source matcher's remaining quantity, then applies the three completed branch theorems.  Its common `SourceResultAt` predicate states that the returned pointers represent the exact `Model.limitL` status, book, and trades, while `OutcomeAt` retains each branch's ownership and allocator facts.  The focused warning-failing build passed in 2.8 seconds under the repository resource limits.

The constrained `clob_limit` artifact check reproduced both checked inputs with `wasm-tools` 1.251.0 in 1.6 seconds.  `Project.lean` now imports `Project.ClobLimit.Spec`, and the aggregate script includes `tools/check-talos-clob-limit.sh` as its eighteenth case.  The constrained aggregate artifact gate matched all eighteen WASM and WAT pairs in 13 seconds.

The artifact gate refreshed shared compiler objects, so the following proof build found eleven stale targets.  It reached its 300-second constrained timeout without a diagnostic while rebuilding `Project.Validate.Spec`; a no-build diagnostic then named that target, `Project.SharedPair.Spec`, both LEB iteration proofs, and seven bounded CLOB targets.  The first four have recorded no-diagnostic timeouts and require the proof divisions specified in `plan.md`, so the unchanged aggregate target will not run again until those divisions restore its missing objects.

## 2026-07-16: Register the `market` Artifact

`Project.ClobMarket.Model.marketL` applies the completed list matcher to an order whose price is the unsigned maximum for side zero and zero for the other side.  Its valid result omits the matcher's remaining taker, while its invalid result returns the input book and empty trades.  A source lemma proves that the price transformation preserves quantity and transfers the matcher's natural-number conservation theorem.

The constrained warning-failing model build passed in 1.2 seconds.  The update gate generated an 8,761-byte WASM input, its WAT rendering, and a 4,912-line Talos program, then built the initial specification in 1.1 seconds.  Functions 0 through 20 are definitionally equal to the `clob_limit` functions, so a closed function-region certificate can transport the complete function 18 theorem without another generated matcher proof.

## 2026-07-16: Transport the `market` Matcher

`FunctionRegion.PortableInstruction` now includes the global, arithmetic, store, and memory operations used by the generated matcher.  A `Shift` also proves equality of memory declarations because memory size and growth inspect that module field.  The generic transport theorem and the earlier limit search certificate pass warning-failing builds in 5.1 and 6.3 seconds.

`ClobMarket.MatchRegion.matchShift` certifies the complete call closure from function 18 through functions 17, 14, 13, 11, 10, and 8.  `ClobMarket.RunMatch.func18_correct` transports the completed limit theorem and retains its exact source matcher result and physical postcondition.  Their focused warning-failing builds pass in 7.6 and 1.0 seconds once their imports are current, so the remaining proof boundary contains only exported function 21.

The first aggregate market build reached its 60-second timeout while rebuilding the stale `ClobLimit.InternalIteration` dependency.  A no-build diagnostic then guided serial target builds through the matcher theorem's linear import chain; `InternalIteration` took 8.9 seconds, `InternalFullTradeUpdate` took 4.8 seconds, and every following target took about one second.  The complete limit function 18 theorem, transported market theorem, and market specification then passed their focused warning-failing builds without another aggregate retry over stale dependencies.

## 2026-07-16: Prove the Valid `market` Branch

`ClobMarket.ExportRegion` transports the shared validity function and both status constants from the limit artifact.  `ClobMarket.Entry` divides function 21 into its validity prefix, valid path, invalid allocation, and final result reads.  The region certificate, helper wrappers, and decomposition each pass focused warning-failing builds in about one second.

The valid path has separate theorems for validity entry, both unlimited-price cases, matcher argument preparation, function 18 result storage, and the three-value epilogue.  `ClobMarket.Valid.func21_valid` composes them into an input-generic theorem returning the exact matcher book and trades with status zero.  Every boundary passes a focused warning-failing build in one to two seconds while preserving the transported ownership, allocator, page, budget, and memory facts.

## 2026-07-16: Divide the Invalid `market` Allocation

`ClobMarket.Entry` now divides the generated invalid program into preparation, free-list search, bump allocation, and finalization phases.  The invalid entry and preparation theorems prove status one, the borrowed input book, capacity eight, and a zero free-list head, while the search theorem proves immediate exit without reading memory.  The frame-generic bump theorem uses the shared fixed-array arithmetic and store definition to prove all six header writes and the heap-top update; its focused warning-failing build passes in 7.4 seconds under the required process limits.

The finalization theorem identifies the length write and allocation-counter update with the shared empty stride-four allocation store.  Two outer compositions reached their 120-second limits without diagnostics because they normalized the concrete forty-nine-local result frame under the exported continuation; an abstract branch-composition theorem and a separate three-read result theorem pass in 3.2 and 4.6 seconds.  `ClobMarket.Invalid.func21_invalid` then passes its focused warning-failing build in 2.1 seconds and states the exact result values, both ownership facts, allocator globals, page preservation, and byte preservation below the old heap top.

## 2026-07-16: Complete Exported `market`

`ClobMarket.Correct.func21_correct` relates every represented valid or invalid input to the exact source `marketL` status, book, and trades.  Its valid outcome retains the transported matcher ownership and allocator facts, while its invalid outcome retains the borrowed book, owned empty trades, exact globals, page count, and below-heap memory frame.  The focused warning-failing theorem and specification builds pass in 1.8 and 1.2 seconds.

The focused artifact comparison passed in 1.3 seconds, and the aggregate artifact gate matched all nineteen WASM and WAT pairs in 15.6 seconds with `wasm-tools` 1.251.0.  The aggregate proof freshness check remains incomplete after artifact regeneration: its no-build diagnostic names the four known long targets `Validate.Spec`, `SharedPair.Spec`, `LebU32.Iter`, and `LebU32.NegIter`, plus seven shorter transitive targets.  The unchanged long targets will not run again until their instruction proofs are divided as specified in `plan.md`.

## 2026-07-16: Register the `depth` Artifact

`Project.ClobDepth.Model` defines the input-order level fold for each side, updating the first matching price or appending a new level with modular `UInt64` quantity addition.  The constrained update generated a 3,602-byte WASM input, a 37,649-byte WAT rendering, and a 1,971-line Talos program; function 3 implements level update or append, function 6 folds one side, and exported function 7 calls it for sides zero and one.  Runtime functions 8 through 11 equal the shared allocate, reset, retain, and release definitions, and their focused warning-failing check passes in 2.2 seconds.

## 2026-07-16: State the `depth` Source Properties

`ClobDepth.Representation` defines the stride-two level layout, flat-word reads, reconstruction theorem, owned fixed-array predicate, and region frame used by later allocation and copy proofs.  `ClobDepth.Properties` identifies the output price sequence, proves membership and uniqueness, states how new and repeated prices affect first-occurrence order, and proves exact per-price modular quantity aggregation with a natural-number corollary under an explicit `UInt64` bound.  Their constrained warning-failing builds pass in 1.7 and 2.4 seconds, and function 3's search, allocation, copy, and final-store regions form the next proof boundary.

## 2026-07-16: Divide the `depth` Level Update

`ClobDepth.Entry` certifies function 3's top-level scan, missing-price branch, found-price branch, and result reads by definitional equality.  Each allocation branch has separate preparation, free-list search, bump fallback, allocation finalization, copy loop, and final-store regions, while the found branch also isolates its bounds guard.  The constrained warning-failing build passes in 1.5 seconds, and the first-price scan is the next semantic theorem.

## 2026-07-16: Prove the `depth` Price Scan

`ClobDepth.Scan.scanProg_spec` proves that function 3 records zero for a missing price and the first matching index plus one otherwise.  Its found outcome retains the exact price and quantity loaded from the represented stride-two level array, while both outcomes preserve the store and expose the generated branch condition.  The source index lemmas, divided scan module, and complete constrained warning-failing scan build pass in 1.9, 1.9, and 3.4 seconds; the missing-price allocation is the next proof boundary.

## 2026-07-17: Prove Missing-Price Preparation

`ClobDepth.MissingFields.missingFieldsProg_spec` copies the new level fields, reads the represented input length, and computes the source and target word counts.  `ClobDepth.MissingPrepare.missingPrepareProg_spec` proves the following capacity calculation, minimum-capacity branch, scratch-local initialization, and free-list-head read.  The explicit twenty- and twenty-four-instruction regions compose definitionally into the original preparation prefix.

The capacity proof follows the established limit allocation pattern by naming the complete emitted expression and rewriting it to `fixedArrayBytesU (levels.length + 1) 2`.  A separate directed reduction selects the empty branch generated by the minimum-capacity test before the final global read.  Both focused warning-failing builds pass in 1.4 seconds under the repository resource limits, and the missing-price free-list search is the next proof boundary.

## 2026-07-17: Prove the Missing-Price Search Exit

`ClobDepth.Entry` now gives the generated free-list search loop an explicit instruction body, avoiding repeated normalization of `drop` and `take` over the complete level-update function.  Its decomposition against generated function 3 remains definitional.  The focused warning-failing entry build passes in 1.5 seconds under the repository resource limits.

`ClobDepth.MissingSearch.missingSearchProg_empty` proves that the loop exits on its first condition when the prepared free-list cursor is zero.  It preserves the store and exact preparation frame without reading a free-node header or payload address.  The focused warning-failing theorem build passes in 1.4 seconds, and the missing-price bump allocator is the next proof boundary.

## 2026-07-17: Prove the Missing-Price Bump Allocation

`ClobDepth.Entry` now names the generated bump branch explicitly while retaining a definitional decomposition against function 3.  `ClobDepth.MissingBump.missingBumpProg_spec` is frame-generic over the allocation need and proves the no-wrap and no-growth branches, all six stride-two header writes, the new heap top, unchanged pages, and the exact scratch frame.  The theorem identifies the result store with the common `fixedArrayAllocBumpStore` transformation.

The focused warning-failing entry decomposition and bump theorem builds pass in 1.6 and 6.7 seconds under the repository resource limits.  The proof reuses the common fixed-array address and page lemmas and changes only the depth local indices and stride.  Allocation finalization, including the length store and allocation-counter increment, is the next proof boundary.

## 2026-07-17: Prove Missing Allocation Finalization

`ClobDepth.Entry.missingAllocFinishProg` is now an explicit twelve-instruction region.  `ClobDepth.MissingFinish.missingAllocFinishProg_spec` is generic over the allocator result and proves the global-two increment, target-root propagation, bounded target-length write, and zero copy cursor.  Its postcondition names one `finishStore` memory transformation and one exact `finishFrame`.

The entry decomposition and focused warning-failing finalization builds pass in 1.8 and 2.0 seconds under the repository resource limits.  The only semantic adapter beyond generated local reduction is the shared equality between `UInt64.toUInt32` and the explicit modulo address used by Talos memory writes.  The missing-price copy loop and its fresh stride-two array facts form the next proof boundary.

## 2026-07-17: Prove the Missing-Price Copy

`ClobDepth.Entry` now names the generated copy body and block-loop program explicitly.  `LevelsAt.frame_write64_flatWordsDisjoint` preserves a represented source level array after one write into a disjoint flat-word destination.  Their focused builds pass in 1.7 and 1.9 seconds under the repository resource limits.

`ClobDepth.MissingCopyInvariant` records unchanged pages and globals, the fresh target header, initialized target length, initial and current source representations, writes confined to the target, and equality of the copied prefix.  Its one-step theorem advances that state after one checked word write, while `ClobDepth.MissingCopy.missingCopyProg_spec` proves the generated loop terminates with all `levels.length * 2` source words copied.  The focused copy theorem and specification builds pass in 2.7 and 1.1 seconds.

## 2026-07-17: Prove the Missing-Price Final Stores

`ClobDepth.MissingStoreFacts.finish` proves that the two appended-field writes preserve the fresh target header and source representation, stay inside the target frame, and reconstruct `LevelsAt` for `levels ++ [{ lprice := price, lqty := qty }]`.  The final state combines that representation with `FreshFixedArrayAt` as an owned level array and retains page and global equality.  The semantic facts module passes its focused build in 2.9 seconds.

`ClobDepth.MissingStore.missingStoreProg_spec` proves the generated 30-instruction store and result-assignment region.  Its continuation receives the semantic final state and exact target values in the working, owner, and pointer locals.  The focused warning-failing theorem and specification builds pass in 2.0 and 1.1 seconds, and end-to-end missing-branch composition is the next proof boundary.

## 2026-07-17: Compose the Missing-Price Branch

`ClobDepth.MissingBranchFacts` connects bump allocation and length initialization to the copy invariant.  It proves the fresh target, initialized length, preserved owned source, exact allocator globals, unchanged pages, and byte preservation below the old heap top.  Its focused warning-failing build passes in 1.5 seconds.

`ClobDepth.MissingBranch.missingProg_spec` composes every generated missing-price phase from the scan outcome through the final result locals.  The theorem returns an owned array for `levels ++ [{ lprice := price, lqty := qty }]`, preserves the owned source, updates global zero to the new heap top and global two by one, and retains pages and bytes below the old heap top.  The branch theorem and specification pass warning-failing builds in 2.7 and 1.1 seconds, and the found-price replacement branch is the next proof boundary.

## 2026-07-17: Generalize the Level-Copy Transition

`ClobDepth.LevelCopyInvariant` parameterizes the target's initialized length and payload word capacity while retaining the source level list and copied source-word count.  Its transition proves one checked word copy, fresh-header and length preservation, source preservation, page and global equality, outside-target byte equality, and copied-prefix extension.  The destination-capacity premise states that every source word has a target slot, which is strict in the append branch and equality in the replacement branch.

`MissingCopyInvariant.CopyState` now specializes the shared state to append-sized targets, and its advance theorem delegates to the shared transition.  The shared module, missing adapter, missing instruction loop, and complete depth specification pass warning-failing builds in 2.4, 1.5, 2.9, and 1.1 seconds; rebuilding all invalidated depth dependents completed within the same constrained specification run.  The found same-length loop will reuse the semantic transition while keeping its different total-word local and instruction body in a separate adapter.

## 2026-07-17: Organize Repository Documentation

Maintained user, language, architecture, verification, demo, design, status, and proof-engineering documents now live under `docs`.  The active `plan.md`, developer entry point `DEVELOPING.md`, repository overview `README.md`, and tool instructions remain at the root.  The development journal also remains at the root, as required by the repository instructions.

The superseded agenda and two early Talos experiment reports now live under `docs/history`.  `docs/README.md` indexes maintained documentation, development records, design records, and historical material without duplicating their contents.  A local-link check examined 20 Markdown files without finding a missing target, and the focused warning-failing `LeanExe.CLI` build passed in 1.4 seconds under the repository resource limits.

## 2026-07-17: Implement the Two-Tool Talos Workflow

The proof workspace now uses `proofs/talos/cases.json` as the single registry for twenty source entries, generated module names, specification targets, and completion flags.  `tools/talos-artifact.js` compiles a registered entry, renders WAT, creates Talos's Cargo-shaped input in an operating-system temporary directory, and retains only ignored WASM, WAT, and `Program.lean` outputs.  `tools/talos-proof.js` repeats generation before a focused or aggregate proof build and validates aggregate specification and runtime imports against the registry.

Both tools run Lake, `lean-wasm`, and the Talos verifier through the required user systemd scope with the four-gibibyte pressure threshold, six-gibibyte hard limit, one-gibibyte swap limit, one-core aggregate quota, reduced CPU priority, idle I/O priority, and explicit timeouts.  They run stages serially, fail when systemd cannot create the scope, and report the failed stage and child status.  The artifact tool fetches the pinned Talos dependency and builds its verifier through the same limits when a clean checkout lacks that binary.

The GCD pilot generated WASM, WAT, and `Program.lean` byte-identical to the former tracked references, then passed `Project.Gcd.Spec`.  A complete artifact run produced byte-identical WASM/WAT pairs and models for all twenty cases before commit `2230fac` removed 68,953 lines of Cargo scaffolding, generated artifacts, generated models, and obsolete wrappers.  A second focused GCD proof passed after the entire persistent `proofs/talos/rust` tree had been removed.

The aggregate proof command regenerated all twenty cases successfully and then exposed tracked proof failures in `Project.ClobPostOnly.AppendTradeStore` and `Project.ClobPostOnly.AppendOrderAlloc`.  Both errors concern fixed-array memory expressions after shared-definition changes, which confirms the stale aggregate state recorded before this workflow work.  The run stopped after those diagnostics, and this migration does not alter either hard proof or the untracked unfinished `Project/ClobDepth/FoundPrepare.lean` file.

The aggregate proof command now validates registry completion flags, specification imports, and runtime model imports before compiling any artifact.  A configuration mismatch therefore fails without starting Lake, `lean-wasm`, or the Talos verifier.  Valid aggregate runs retain the same serial generation and proof stages.

## 2026-07-17: Prove Found-Price Preparation

`FoundPrepare.foundPrepareProg_spec` now builds, and the focused warning-failing `Project.ClobDepth.FoundPrepare` target passes in about three seconds under the repository resource limits.  The theorem steps the generated found-branch preparation region from the scan outcome frame to the allocation continuation frame.  This closes the first entry in the remaining depth order.

The draft proof mismatched the generated decode in three ways.  `simp` rewrites the `ltUI64` guard `x < 1` to `x = 0`, so both decode sites now use `rw [if_neg hEncoded]` followed by `rw [if_neg (by simp)]`, the idiom from the missing preparation.  `simp` also cancels `i + 1 - 1` during instruction stepping, which made the named subtraction rewrite and its two supporting hypotheses dead.  The proof tail now follows the program's order: reload the level count at the source address, pass the index bound check through `wp_iff_cons`, then read the matched quantity.

The generated locals proved `prepareFrame` wrong at two entries.  Scratch locals 26 and 27 keep the encoded index and the constant one after the second decode, so the frame now records `UInt64.ofNat i + 1` and `1` there.  Allocation preparation, the next depth boundary, consumes this corrected frame.

## 2026-07-17: Prove Found-Price Allocation Preparation

`FoundAllocPrepare.foundAllocPrepareProg_spec` passed its focused warning-failing build in 1.6 seconds on the first attempt.  The theorem follows the `MissingPrepare` capacity pattern with `fixedArrayBytesU levels.length 2` in place of the append capacity, and it keeps the empty free-list premise on global 1.  Its input state is the corrected `FoundPrepare.prepareFrame` with the branch flag consumed, so the found-branch composition can pass through the allocation conditional and continue with `allocFrame`.

## 2026-07-17: Adapt Search, Bump, and Finish for the Found Branch

`MissingSearch.missingSearchProg_empty` now takes its local frame abstractly with length, empty-stack, and zero-head hypotheses, matching the style of the bump and finish theorems.  The `MissingBranch` composition passes its recorded `prepared` frame facts, and the missing chain rebuilt without further change: the search module in 1.4 seconds and the branch composition in 2.6 seconds.  One search theorem now serves both level-update branches because `foundSearchProg` and `foundBumpProg` equal their missing counterparts by definition.

`FoundFinish.foundAllocFinishProg_spec` adapts the finalization to the found program, which stores the unchanged level count from local 16 where the missing program stores the extended length from local 17.  It reuses `MissingFinish.finishStore` and `MissingFinish.finishFrame`, and its focused build passed in 1.9 seconds on the first attempt.  With an abstract frame, `rintro` substitutes the frame hypothesis for the loop variable, and the final frame equality follows from structure eta once the empty value stack is rewritten.

## 2026-07-17: Prove the Found-Price Same-Length Copy

`FoundCopyInvariant` specializes the shared level-copy state to target length `levels.length` and payload `levels.length * 2`, and its advance theorem passes `le_rfl` for the source-fits bound.  The cursor frame, frame-zero theorem, and loop measure come from `MissingCopyInvariant` unchanged because both branches use cursor local 19.  `FoundCopy.foundCopyProg_spec` differs from the missing loop theorem in the total-holding local, 17 rather than 16, and in target bounds stated over the same-length payload.  Both modules passed their focused warning-failing builds on the first attempt, in 1.4 and 2.6 seconds.

## 2026-07-17: Prove the Found-Price Quantity Replacement

`FoundStoreFacts` reuses `MissingStoreFacts.appendLevelStore` with the matched index as its slot, because the two generated stores write the same relative words.  The new `replaceStore_read_other` lemma preserves any unwritten level word on either side of the replaced pair, which the append case never needed, and the `finish` theorem reconstructs `levels.set i level` through `List.getElem_set_self` and `List.getElem_set_ne`.  `ReplaceState` states ownership of the replaced array, the preserved source representation, and the same-length outside-region frame.

`FoundStore.foundStoreProg_spec` steps the two stores from the completed copy frame and leaves the target pointer on the stack as the allocation-branch result, so its continuation frame is the copy frame with one stacked value.  The generated stores index by the matched-index local 15 where the missing branch uses the length local.  Both modules built in under three seconds, with two set-lemma argument fixes and the recorded `hValues` bridge for the unused-variable linter.

## 2026-07-17: Compose the Found-Price Branch

`FoundBranchFacts` mirrors the missing branch facts with same-length capacity `fixedArrayBytesU levels.length 2` and a length word equal to the unchanged level count, and its `ResultState` returns ownership of `levels.set i level`, the preserved source array, the exact allocator globals, page equality, and bytes below the old heap top.  `FoundBranch.foundProg_spec` composes preparation, the guarded allocation conditional, allocation preparation, the shared empty search, the generic bump, the found finalization, the same-length copy, and the replacement stores from the scan handoff frame.

The value-returning allocation guard needed no new machinery: `wp_iff_cons` with a positive flag enters the branch, the phase theorems chain inside the branch continuation with an empty trailing program, and one closing simplification consumes the empty program, re-enters the outer continuation with the returned pointer, and executes the three result-local assignments.  The composition builds in 3.1 seconds.  One import gap surfaced: no earlier found module imported `FoundAllocPrepare`, so the composition file imports it beside the branch facts.

## 2026-07-17: Prove Function 3 with One Update Result

Two new source lemmas in the properties module state `addLevelL` exactly: a missing price appends one level, and a matched index replaces the quantity through `List.set` with the summed modular quantity.  `Func3.UpdateResult` uses them to give both branches one conclusion: the returned array represents `addLevelL levels price qty`, its capacity is the fixed-array capacity of the result length, global 0 advances by that capacity, global 2 increments, pages hold, the input array survives, and bytes below the old heap top are unchanged.

`Func3.func3_spec` selects the branch through `Scan.scanProg_spec`, enters the scan conditional with the matched flag, and finishes by reading the two result locals over the abstract final frame of either branch.  The theorem keeps branchwise fit and disjointness premises, which the function 6 loop invariant must supply for the result-length capacity of each step.  The focused build passes in 2.7 seconds, and the depth chain up to the composition rebuilds in under seven seconds per module.

## 2026-07-17: Prepare Function 6 Slices and the Function 3 Call

`Entry.func6_decomposition` divides generated function 6 into a length-reading header, one shared empty-array allocation slice used twice with different destination locals, the order-count minimum, the per-order fold loop, and the result tail.  The two generated allocation regions are instruction-identical up to the final `localSet`, which the decomposition keeps as separate singleton programs.  The slices were extracted mechanically from the generated model and the decomposition holds by `rfl` in a 2.3-second `Entry` build.

`Func3.func3_terminates` wraps the function 3 composition as a `TerminatesWith` statement through `TerminatesWith.of_wp_entry_for`, following the `ClobLimit` pattern.  Call arguments appear in stack order, so the argument list reverses the parameter order, and the closing simplification needs `Function.numParams` to reduce the result-shape arithmetic.  The fold loop can now step each matching order with `wp_call_tw` at the current store.

`Func6Alloc.allocProg_spec` proves the shared empty-allocation slice once, following the `ClobLimit` empty trade-array adapter with stride two, the depth local indices, and a stacked result root for the caller's destination local.  `allocStore` records the exact heap-top and counter globals and the empty owned level array at the bump root, and the focused build passes in 9.1 seconds.

`Func6Fold` defines the fold state after any order prefix: represented levels through `depthSideL` of the taken prefix, the match count, and exact heap-top, result-root, owner, and capacity recursions.  Its lemmas bound the level count by the match count, place root plus capacity at or below the heap top, and bound the heap top by `g0 + 112 + k * stepBytes count` with `stepBytes count = 56 + 16 * count`, which the loop invariant will use to discharge every per-step fit premise.  The successor cases rewrite with equation lemmas and expand the one nonlinear product for `omega`.

`Func6Loop` states the fold loop invariant: a frame predicate over the side parameter and the orders, owner, root, cursor, and limit locals; a store predicate with pages, exact globals through the fold recursions, the owned result array, the preserved `OrdersAt`, and the byte frame below the initial heap top; and the invariant as an existential over the consumed prefix.  `foldState_initial` establishes the store predicate at prefix zero from the double empty allocation, converting the heap-top, counter, and root values through one no-wrap bound.  The module builds in 2.5 seconds with the semantic step theorems included.  `FoldState.step_match` transports a function 3 `UpdateResult` at the invariant's exact globals into the invariant at the next prefix, deriving every no-wrap bound from the single budget premise `g0 + 112 + count * stepBytes count < 4294967296` through `foldTop_le` and the new `foldTop_ge`.  `FoldState.step_skip` collapses the recursions for a non-matching order.  The remaining function 6 work is the loop body instruction proof and the composition.

## 2026-07-18: Prove the Function 6 Fold Loop Body

`Func6Loop.foldLoop_spec` proves the generated fold loop against the invariant.  The exit test closes through the block continuation with the invariant frame at the full count, the five order-field loads rewrite through the `OrdersAt` bounds and reads in the simp normal form, and the generated three-stage side flag reduces branchwise.  The matching branch applies `wp_call_tw` with `Func3.func3_terminates` at the invariant's exact globals, deriving all sixteen call premises from the fold bounds and the single heap budget, and both branches close with the semantic step theorems and per-field frame reasoning through the local-set chain.

Three elaboration findings from this proof: the stack values normalize to the `getD` form of `getElem!`, so the call site needs one `simp only` with the reversed bridge before `wp_call_tw`; the `ofNat` successor equation loops as a simp argument because the default set rewrites in the opposite direction, so cursor and measure goals close without it; and the block-exit frame carries the block-entry value stack, which the invariant's empty-stack field discharges.  The focused warning-failing build passes in 10 seconds.

`Func6.func6_terminates` composes the whole per-side fold: the two length reads close through the `OrdersAt` head as conjunction obligations, the shared allocation adapter applies twice with the allocated-store global lemmas, the degenerate minimum reduces through one conditional, and the loop theorem consumes the invariant seeded by `foldState_initial` with the two root conversions.  The result tail reads the owner and root over the abstract final frame, and the wrapper returns the fold state at the full prefix with the stacked root and owner values.  The composition builds under `--wfail` in 3.3 seconds.

`Func7.func7_terminates` composes the two side folds through the function 6 calls.  The second call runs at the first call's exact heap top and counters, the first result array survives the second fold through the below-heap byte frame, and the full-prefix lemma turns both fold states into the source side folds.  `Func7.Result` states ownership of the bids and asks arrays with `depthSideL` contents, the preserved orders representation, the exact three allocator globals, page equality, and bytes below the initial heap top.  The one presentation repair removes a modulus that the closing simplification reintroduces on the second fold's base.  The build passes under `--wfail` in 3.8 seconds.

## 2026-07-18: Complete the `clob_depth` Artifact

`Project.ClobDepth.Spec` now imports the function 7 chain and restates the returned arrays through `Model.depthL`, beside the exact modular per-price aggregation and its bounded natural-number interpretation from the source properties.  The registry entry carries `complete: true`, and the aggregate `Project.lean` imports the depth specification.  The focused gate `tools/talos-proof.js check clob_depth` regenerated the model from the current source and compiler and passed the full specification build.

## 2026-07-18: Repair the Recorded PostOnly Failures

Both recorded aggregate failures were unfolding gaps after the shared allocation definitions moved their header writes into `fixedArrayHeaderMem`.  The trade-store proof's fresh-array conversion and the order-allocation proof's below-array byte frame each needed that one definition added to their closing `simpa` sets.  The focused warning-failing builds pass in 12 and 7.1 seconds.

## 2026-07-18: Aggregate Gate Reaches Its Stage Timeout

The 2026-07-18 aggregate run regenerated all twenty artifacts and then hit the tool's twenty-minute aggregate-build cap: `systemd-run` exited with status 124 inside `tools/talos-proof.js check --all`.  The previous aggregate run failed fast at the two `ClobPostOnly` proofs, so this run is the first to proceed past them into the modules with recorded no-diagnostic timeouts.  The result is an unresolved gate rather than a proof failure.  The planned division of `Project.Validate.Spec`, `Project.SharedPair.Spec`, `Project.LebU32.Iter`, and `Project.LebU32.NegIter` is the recorded response, and it now folds into the proof-infrastructure overhaul.

## 2026-07-18: Build the Shared Proof Infrastructure

The overhaul replaces the recorded per-module idioms with shared infrastructure in `Project.Common`.  `u64_omega` closes `UInt64` and `UInt32` equalities, inequalities, and their negated forms by one conversion pass through the `u64_toNat` simp set and `omega`; the unconditional modulus normal forms make several bounds that the hand proofs carried unnecessary, including the successor conversion `ofNat k + 1 = ofNat (k + 1)`.  `getElem_of_some` converts an optional element fact to its proof-carrying form with an autoparam bound, replacing the five-line conversion blocks at 157 sites.  `wp_run_with` is the one instruction-stepping macro behind the 59 per-module variants, and `wp_guard_pos` and `wp_guard_neg` name the conditional-entry idiom.

`FixedArrayAllocation` gains a read interface for `fixedArrayHeaderMem`: the six header reads, the outside-read frame, and the page fact, stated once so proofs stop unfolding the write chain.  The six reads hold without any address bound because the disjointness side conditions are unconditional modular facts.  `Project.InfraTest` guards the tactic contract with focused examples.  The rule against parameterizing shared theorems over generated locals is withdrawn in the proof notes, and the migration now proceeds artifact by artifact from the beginning of the workspace.

## 2026-07-18: Sweep Migration and Lake Worker Scheduling

The scripted sweep replaced 139 of the 157 optional-element conversion blocks, all ten depth macro clones plus most clones across the other trees, and 88 standalone bound proofs with the shared infrastructure.  The depth chain and the matchFuel, limit, and market stacks verified clean.  Six local macros remain by design because they use `simp only` or `simp_all`, which are different reduction disciplines from the shared macro.

The wide verification build for the remaining stacks exposed a scheduling gap in the resource policy: Lake has no job-count option, and it placed `ClobMatchFuel.FindBest` and `ClobPostOnly.FindBest` — each about 3.8 gibibytes and six minutes solo — into the one constrained scope together, where they split a single core, crossed the memory-pressure threshold, and made almost no progress for forty minutes.  The build was stopped, the two large modules now build alone before any wide target, and both belong on the division list beside the four recorded no-diagnostic modules.  A third latent header-unfolding gap surfaced in `ClobPostOnly.AppendTradeBranchStore`, unreached by earlier aggregate runs, and took the same one-definition repair; its focused build passes in 13 seconds.

## 2026-07-18: Serialize Lake Jobs (Corrected)

The wide verification build degenerated a second time: Lake scheduled four multi-gibibyte workers into the one constrained scope, resident memory reached about sixteen gibibytes against the six-gibibyte ceiling, and throughput collapsed.  The first fix attempt was wrong: `AllowedCPUs=0` does not bound the pool, and the probe that appeared to confirm it had a linear dependency chain that would have run one worker regardless.  A later four-worker collision under the affinity pin exposed the error.  The valid control is `LEAN_NUM_THREADS=1`: Lake schedules builds on Lean's task pool, and a four-independent-target test under the variable ran exactly one worker.  The policy, the Talos tools, and the status report now carry the environment variable, and the affinity property is removed.

`PairFree.Spec` is intrinsically heavy: it ran 85 minutes solo without a diagnostic under the serialized policy, and a controlled rebuild with the sweep edits stashed also exceeded a twenty-minute cap, which shows the five bound-proof conversions in that file did not cause the slowness.  The module joins the division list beside `SharedPair.Spec` and the other recorded no-diagnostic modules.  Serialization itself is confirmed effective: `ClobCancel.Spec` built in 35 seconds where the run with concurrent workers had held it for 53 minutes.  The heavy modules that took forty minutes or more under concurrent workers build at full speed serially: `ClobPostOnly.FindBest` in 207 seconds and `ClobMatchFuel.FindBest` in about six minutes.

## 2026-07-18: Sweep Warnings and the PushTwice Classification

The wide build over the remaining stacks verified the ClobLimit conversions, most of the ClobMarket chain, and `AppendBang.Spec`, and reported two problems.  `ClobMarket.InvalidSearch` failed with an unknown identifier because the hand conversion to `getElem_of_some` did not add the `Project.Common` import; the import is added.  `PushSize.Spec` reported nine simp calls with unused arguments, all older than the sweep: this warning-failing build is the first over that file since the arguments became unnecessary, and the aggregate tool's build does not turn warnings into failures, so the aggregate gate never reported them.  Each call now keeps the one argument the linter left unflagged, and the call whose arguments were all flagged keeps none.

`PushTwice.Spec` ran 46 minutes without finishing under the serialized policy.  It belongs to the same group of byte-array example proofs as `PairFree.Spec` and `SharedPair.Spec`, and the PairFree control rebuild showed the sweep's edit type does not cause slowness in that group, so PushTwice joins the division list without a second control run.  The division list is now `Validate.Spec`, `SharedPair.Spec`, `LebU32.Iter`, `LebU32.NegIter`, `PairFree.Spec`, and `PushTwice.Spec`.  The wide build is relaunched without PushTwice.

## 2026-07-18: Assessment of the Depth Duplicate-Module Merge

The planned merge of the depth branch pairs is rejected after reading the diffs.  `FoundCopyInvariant` already imports `MissingCopyInvariant` and reuses its loop frame and measure, so the pair's remaining lines carry the branch-specific content: the missing branch appends into a length-plus-one array under `MissingStoreFacts.FinishState`, while the found branch replaces in a same-length array under `FoundStoreFacts.ReplaceState`.  A parameterized module would need an abstraction over those two state records and a length parameter through every statement, which costs more lines and review effort than the roughly 150 duplicated lines it removes, and it would rebuild a verified tree.  The pairs stay, and the shared parts stay factored where they already are.

## 2026-07-18: Slow-Module Division, First Measurements

`Validate.Spec` timed out at 25 minutes with no output, so the recorded timeout stands under the serialized policy.  The file is now five files: `Digit`, `Read`, `Invariant`, `Loop`, and the reduced `Spec`, all in the original namespace with `private` removed where a definition crosses files.  The divided build isolates the entire cost in one theorem: `Loop.lean`, holding `func2_terminates`, elaborates in 1560 seconds, and the other four files build in seconds.  The split exposed two unused `vFrame` simp arguments that the monolithic file never reported because it never finished a warning-failing build; both are pruned.  Division at theorem boundaries therefore isolates cost and adds checkpoints, and it does not reduce the heavy theorem's own elaboration time.

`LebU32.Iter` ran about 89 minutes alone without finishing, after `Copy` and `Defs` built in seconds, so its recorded timeout also stands under the serialized policy.  The file already carries a note that it was split from a larger proof, its single theorem disables asynchronous elaboration, and its proof is thirteen `wp_run` calls with no single unusual step.  `PushSize.Spec` at about 450 lines builds in 39 seconds while `PushTwice`, whose theorems are each about that size, exceeded 46 minutes, so elaboration cost grows much faster than proof length.  `PushTwice` and `PairFree` are now divided at theorem boundaries (`Base`/`Empty`/`Reuse` and `Base`/`Builds`/`Frees` under reduced `Spec` files); the divided `PushTwice` build measures whether a `PushSize`-sized piece regains `PushSize`-like speed, which decides between per-theorem slicing and a deeper cause for the remaining modules.

## 2026-07-18: Root Cause of the Slow Modules Is Working-Set Size

The divided `PushTwice` tree builds in 56 seconds where the monolithic file exceeded 46 minutes, and the divided `PairFree` pieces `Base` and `Frees` build in 1.6 and 19 seconds while the 804-line `Builds.lean` ran 178 minutes without finishing.  A diagnostic build of `LebU32.Iter` under a raised, enforced scope (pressure threshold 9 gibibytes, hard cap 10) settled the mechanism: the worker reached the 9-gibibyte threshold, consumed under two minutes of CPU in fifteen minutes of wall time while stalled in reclaim, and the kernel OOM killer ended the scope at a 9.1-gibibyte peak when other user programs claimed memory.  The heavy theorems hold working sets above what this 15-gibibyte machine can grant, so under the standard 4-gibibyte threshold they run throttled for their entire build, which produced every recorded no-diagnostic timeout.

Consequences.  Raising the memory policy cannot fix these modules on this machine, and one-time long cached builds cannot either, because `PairFree.Builds` and `LebU32.Iter` do not finish in the times tried.  The fix is to reduce the per-process working set: divide files at theorem boundaries where several theorems share a file, and slice the remaining heavy single theorems (`PairFree.Builds`, `SharedPair.Spec`, `LebU32.Iter`, `LebU32.NegIter`) into staged lemmas with explicit intermediate frames.  Goal size appears to drive the working set: the slow theorems step the largest function bodies with the most locals under generic postconditions.  `Validate.Loop` completes in 26 minutes under the standard scope and stays as-is for now.

## 2026-07-19: The Cliff in the Heavy Proofs, Measured

A bisection of `LebU32.Iter` located its cost to one tactic: everything through line 253 elaborates in 15 seconds, and the six-way `refine` discharging the header-write bounds at line 255 exceeds ten minutes.  A sequence of controlled probes then separated every candidate cause.  The statement elaborates in 7 seconds.  The full premise set with the same six bound goals and a `True` tail discharges in 15 seconds, which rules out the premises and `omega`.  With the `wp` application in the tail, every structural tactic hangs: a `refine` with three or more real components, six `have` steps, a bullet sequence, and a `simp only` rewrite of the conjuncts all exceed ten minutes, while up to two components stay free.  The rule that fits all measurements: a structural tactic against a goal that carries an unreduced `wp` application over literal program and store terms is the pathological case, and the `wp` stepping tactics themselves handle those goals at ordinary cost.

Extracting the site into a fresh lemma did not finish either: a `wp`-only lemma holding the proof text after the cliff still exceeds 30 minutes at 6.7 gibibytes, so the copy-loop body inside that text contains further sites of the same class.  The build artifacts show the whole `LebU32` tree elaborated once on July 9, before the resource policy, with a 12-megabyte `NegIter.olean`, so the proof text is valid and the cost is real elaboration cost, paid once unconstrained.  The four remaining heavy modules (`LebU32.Iter`, `LebU32.NegIter`, `SharedPair.Spec`, `PairFree.Builds`) share the pattern.  Repair by surgery means one extracted lemma per cliff site with the count per file unknown; the alternative is an unconstrained build exception, which the policy forbids for cause.  The choice is recorded as open.

## 2026-07-19: Local Variants Exhausted for the Heavy Proofs

Two further probes close the survey.  Single-component `refine` steps chained six times hang, though one such step alone is fast, so the budget that matters is the total number of structural operations against the goal, and no reordering or regrouping of the existing discharge text stays inside it.  The `wp`-only extracted lemma also exceeds 30 minutes because the copy-loop body inside it repeats the pattern.  The distinguishing feature of the sites, refined once more: the goals at the hanging sites carry the `wp` term inside an unreduced match on a global read, over literal instruction, store, and frame terms, while the goals the same tactics handle at ordinary cost carry `wp` over named definitions and variables.  The four heavy modules were each elaborated once on July 9, unconstrained, so their text is valid and the cost is real.

Three options remain, and the choice is the project owner's.  First, rewrite the four proofs in the discipline the fast trees use: named-state lemma pipelines over definitions instead of literal states, which the depth and limit trees show elaborating in seconds; this is a re-proving effort of about 2,300 lines.  Second, a sanctioned unconstrained build for these four modules on an idle machine, which the resource policy forbids for cause and which would recur at every invalidating change.  Third, remove the four example artifacts from the aggregate gate and keep the CLOB suite as the verified surface, which is a scope reduction.  No further build attempts on these modules until the choice is made.

## 2026-07-19: Iter Repairs Banked, Final Cliff Open

Four of the five cliffs in `LebU32.Iter` are repaired and probe-verified: the allocation transition closes with pre-stepping bound facts, a match reduction, and one `and6_and` application; the loop-initialization write chain closes through the `posWritesLo` helper; the have block in the final-byte arm dissolved into six private lemmas applied as terms; and the byte bullet's nested side proofs are flat.  The repairs added `posBuf1`, `posKadd`, `posNw`, `posByte`, `posFinal`, `getlAppend`, `getkAppend`, and `posGlobals` as private lemmas, and `and6_and` in `Project.Common`.

The fifth cliff is the invariant-instance discharge after the final byte: focusing any of its globals conjuncts hangs, packed projections hang through the multi-component rule, `on_goal` discharges hang at the focus step, and a `trace_state` on the parent goal cannot even print it inside ten minutes, though `sorry` accepts it at once.  The instance term resists every traversal-based operation while the surrounding stepping stays cheap.  The planned repair is the deep restructure: extract the final-byte arm as a postcondition-generic lemma entered at the named-state boundary.  That work is deferred until after `PairFree.Builds` and `SharedPair.Spec`, whose recorded refine shapes match the first cliff, where the repair is known and mechanical.

## 2026-07-19: Builds Mapped, First Site Repaired

`PairFree.Builds` carries two cliffs.  The first, at the first allocation's write bounds, is the Iter transition shape exactly and is repaired the same way: six bound haves beside the file's own working have block, the global-counter match reduced before the split, and one `and6_and` application; the probe past the site runs in 16 seconds.  The seven-component refine at the second allocation measured healthy, 3.5 minutes for its whole prefix, so component-count alone is not the trigger there and no change was made.  The ladder over the remainder grows mildly to 257 seconds at line 680 and hangs at 750: the second cliff is the header read-back region, bullets of rewrite chains with up to fourteen `read64_write64_ne` terms each.  The planned repair is the pack pattern that cleared Iter's write chain and globals: one private lemma stating the read-back facts over the final store, proved in fresh context with the same chains, with the bullets becoming single projections.

## 2026-07-19: Handoff State for the Heavy-Proof Repairs

The working discipline, verified across every repair so far: structural tactics against the pathological goals are limited to about two live components; facts move into private pre-stated lemmas applied as terms with ambient hypotheses as arguments; side proofs stay flat with no `by` nested inside a term inside another tactic block; stuck matches on global reads get reduced by an equation rewrite before any split; and multi-conjunct discharges go through packed lemmas (`and6_and` in `Project.Common`, or a full-instance pack) so the pathological conjuncts are never focused as goals.

Per-file state.  `Validate` and `PushTwice`: divided, verified, committed.  `PairFree`: `Base` and `Frees` verified; `Builds` has its first cliff repaired and its second mapped to the header read-back bullets at lines 681 through 750, where the final store is a fourteen-write chain printed in full in the scratchpad log `buildsprobe5.log`; the planned repair is a private read-back pack lemma stating those read conjuncts over the chain, with the bullets becoming projections.  `LebU32.Iter`: four cliffs repaired; the fifth is the invariant-instance discharge in the final-byte arm, where focusing any globals conjunct hangs and even the pretty printer cannot traverse the goal; the planned repair is extracting the arm as a postcondition-generic lemma entered at the named-state boundary.  `LebU32.NegIter` mirrors `Iter` and waits for `Iter`'s completed pattern.  `SharedPair.Spec` carries the same recorded refine shapes and is unmeasured beyond that.

## 2026-07-19: Builds Read-Back Pack Fully Specified

The fine ladder over the read-back bullets shows accumulating cost, 255 to over 600 seconds as bullets discharge, so no single bullet carries the hang and the repair must avoid focusing those goals at all.  The final refine's twenty conjuncts are distilled in the scratchpad file `buildsFinal-spec.txt`: conjunct one is a bound the site keeps as an inline omega, and conjuncts two through twenty become one private lemma, `buildsFinal`, over a memory parameter `M` bound to the fourteen-write chain by a defining equation premise, so each conjunct states one short read over `M`.  The site then closes with a two-component constructor, the discharge form measured safe throughout: the omega bound and the pack application.  The pack's proof takes the existing bullet texts after substituting the chain equation, and its premises are the have block above the refine plus the theorem hypotheses, completed by compile iteration.  The same two-component pack closure is the candidate for the open Iter invariant discharge.

## 2026-07-19: Sibling Poisoning Confirmed, Body-Lemma Design Fixed

The copy-loop case arms of `PairFree.Builds` are each fast in first position and hang in second, under both orders, including pure rewrite steps.  Assignments in one arm degrade the sibling goal's term for every traversal-based operation.  The complete fix is the architecture the original author used for `LebU32`: the whole loop-body obligation becomes one private lemma, `buildsBody`, whose conclusion is the match-headed body goal — extracted in full, 224 lines, to the scratchpad file `buildsBody-goal.txt` — with the case split inside the lemma's fresh context, and the site reduced to one `exact`, the assignment form that poisoned goals accept.  Its premises are the copy-loop invariant components from the introduction pattern plus the theorem-level facts.  The verified pieces so far: the `buildsFinal` pack elaborates clean alone, the pack site unifies in seconds, the copy arm's lemma-based guard reduction works in first position, and `buildsNotLe` carries the guard fact.

## 2026-07-19: Transcription Route Closed, Generic-Postcondition Design Fixed

Stating `buildsBody`'s conclusion from printed goals fails for cause: the pretty printer's output for these terms is not re-elaborable.  Sharing bindings print in a form that re-elaborates to different terms, deep instruction lists elide under every print option in some context, and match patterns print as compound names the parser rejects.  Three regeneration rounds each removed one class of damage and exposed the next.  The conclusion cannot come from prints.

The correct form is the one `posIterLemma` already uses: the body lemma takes the postcondition as a variable with one premise per leaf outcome — a trap premise, a repeat premise taking the re-established invariant and measure decrease, and an exit premise taking the done-state facts — so no concrete continuation appears in any statement.  The proof's leaves change from proving invariant instances inline to applying the matching premise.  The site instantiates the premises with the loop rule's own continuation, where each instantiation is small.  This is a fresh construction over the existing case-block text, next session's first task.  `Builds.lean` is reverted to commit f522269, which is valid and carries the verified pack, guard lemma, and arm swap; the working measurements and the failed-route logs are in the scratchpad.

## 2026-07-19: Generic-Postcondition buildsBody Works, One Extraction Left

The generic-postcondition body lemma is constructed and sound: with the site's exit bullet replaced by `sorry`, the whole file elaborates in 22 seconds, including the body lemma with both arms, the repeat bullet, and the trap bullet.  The pattern followed `posIterLemma`'s call shape exactly: the postcondition argument is an underscore the elaborator infers, the trap premise discharges by `rfl`, the repeat premise by introduction, stepping, and the hypothesis, and the frame passes as a variable with a reflexivity equation.  Iteration fixes along the way: trap rewriting after each stepping call inside the lemma, since a generic postcondition no longer collapses the trap branch; goal rewrites instead of destructuring for the exit equations, since substitution eliminated the surviving store variable; and the allocation-size bounds restored to the premise set.

Two small residues: an unsolved goal at the lemma's line 359 and unused simp arguments at line 320, both localized.  The one real task left in this file: the site's exit bullet holds the phase-two text, which alone costs the thirty-minute timeout; it becomes a `buildsPhase2` lemma at the post-exit stepping point by the same template — deep-trace the goal there, define the after-block program, state generically over the postcondition, move the text, close the bullet with one application.  After `Builds` is green: Iter's fifth cliff by this same template, then `NegIter`, then `SharedPair`.

## 2026-07-19: One Extraction Remains for Builds

With the frame unfold added, the exit bullet still exceeds thirty minutes while everything else in the file elaborates in 22 seconds, so the phase-two text requires the same extraction the body received.  The continuation step, exactly: re-run the deep trace at the exit bullet's post-stepping point now that the frame unfold precedes it; from the print, define the after-block program and state `buildsPhase2` generic over the postcondition with the exit state's facts as premises, by the `buildsBody` template; move the phase-two text into it, leaving the pack exact as its leaf; close the site's exit bullet with one application.  Also outstanding, both localized: an unsolved goal at the body lemma's copy-arm frame bullet, and the repeat bullet's two omega goals at the site, whose counterexamples are in the v6 and v7 logs.

## 2026-07-19: Builds Decomposition Stands, Phase-Two Interior Remains

The generic-postcondition decomposition of `PairFree.Builds` is structurally complete and its outer levels are verified: the body lemma with both arms, the site with small premise bullets, the result pack, and the guard lemma all elaborate fast in isolation, and the twelfth build iteration has no errors.  The remaining cost sits inside `buildsPhase2`: its moved text carries the second-allocation have blocks and multi-component refines, which reproduce the known slow shapes one level down, and a fresh context does not rescue them, consistent with the `IterAlloc` measurement.  The continuation bisects `buildsPhase2`'s interior with the standard cut ladder and applies the established per-site treatments — private fact lemmas applied as terms, flat side proofs, early match reduction, and packed conjunction closures — exactly as the four repaired Iter cliffs and the two repaired Builds sites received.  The working-directory drift that misdirected two build commands is a recorded hazard: run every lake command from the workspace root by absolute path.

## 2026-07-20: Phase-Two Interior Mapped to Two Blocks

The re-ladder after the modulus pack shows the same profile, and the region views identify the real content: phase two contains the pair-literal fill loop — an inner loop rule application whose body case is another stuck-match-hostile zone holding the `stB` store facts — and a block of chain-read haves (`hcell`, `hmagic2`, and peers) whose statements each inline the full fourteen-write chain.  The chain-read block takes a second result-pack lemma, `buildsCells`, over a memory parameter bound by equation exactly as `buildsFinal` is built, with the haves becoming projections.  The store-fact block hoists to the zone before the inner loop's stepping or becomes premises of a small pack over `stB` stated as a parameter with its defining equation as a premise.  The unified rule from all measurements: goals with stuck matches — an opaque postcondition or an undecided scrutinee — are hostile to context extension and to multi-component structural steps, while rewrite-class tactics and single-term applications stay cheap; every repair converts work in hostile zones into pre-stated lemmas applied as terms.

## 2026-07-20: Cell Pack In, Store-Fact Pack Next

`buildsCells` is installed with the three chain-read haves as projections; its two below-chain bullets need premises for the base-store reads at `g0` and `g0 + 8`, whose site proofs belong with the rest of the pending store-fact block.  The consolidation: one lemma, `buildsStB`, parameterized over `st2` with the banged store written inline, supplying as one conjunction every `stB` fact the phase-two text uses — the globals reads, the page equation, the header reads including the two the cell pack needs, and the pointer facts.  The site keeps a single `have` binding its application, inside the one-operation budget that measured tolerable, and every use becomes a projection.  The file at this commit has three localized errors: the two cell-pack bullets pending their premises and one site mismatch at line 875; the fallback valid state is commit 5d26f29.

## 2026-07-20: Phase-Two Drain List

Thirty-three top-level haves sit in phase two's hostile zone: fifteen store facts over the banged store (`hg0S`, `hpgB`, `hg2S`, `hmagic2e`, `hrc2e`, `hg3S`, `hlenB`, `h0B`, `h2B`, `h3B`, `hh0e`, `hh24e`, `hg1B`, `hg4B`, `hg5B`) and eighteen arithmetic facts over the theorem variables (`h48` through `hpne`, including the six `hsubB` header offsets and `haddr40`).  The consolidation is two pack lemmas — the store facts over `st2` with the banged store inline, premised on the copy-loop facts, and the arithmetic facts premised on the size bounds — with every use becoming a projection and the two cell-pack premises supplied from the store pack.  Internal ordering inside the packs is free since fresh contexts admit haves.  The inventory script and line numbers are reproducible from this journal's date entry.

## 2026-07-20: Loop-Body Scaffold and Frame Macros

`Project.WpScaffold` is built and verified: `wp_loop_body_intro` turns a
postcondition-generic body lemma — trap, repeat, fallthrough, and break
premises — into the loop rule's body obligation, so no proof writes a
match continuation again; `bytes_frames` peels byte-preservation through
chains of word and byte writes; and `read_frames8` extends the existing
`read_frames` over byte writes.  All three follow the measured
discipline: rewrite-class discharge and single-term application in
stuck-match goals.  The scaffold builds in 103 seconds in its own file,
so consumers pay no `Common` invalidation.

## 2026-07-20: Folded Frames Cut Validate.Loop From 1560 to 15 Seconds

Stepping cost is simp search times term size, and the term size came
from the frame: `wp_run` unfolds every local read and write into walks
over the 24-element frame literal.  The fix keeps the frame folded
behind its definition.  `tools/gen-frame-lemmas.py` generates, per
frame, `@[frame_step]` lemmas for get, set?, validIndex, lengths, bare
projections, and record-form set-refolds; `Project.FrameAttr` registers
the simp set; and `wp_run_folded` in `Project.WpScaffold` steps with
`wp_simp` plus `frame_step` while omitting the raw `Locals` operations,
so the definition never opens.  Values-transparency lemmas
(`get_values`, `set?_values`, `validIndex_values`, `values_values`) let
the folded frame survive operand-stack traffic.  On
`Project.Validate.Loop` the module went from 1560 seconds to 15, with
`Validate.Spec` and `Validate.Read` unaffected.  Two rules from the
iteration: a refold lemma whose right side is a record of projections
matches itself and loops simp, so set-refolds must demand a `.set` on
the left; and boundary goals — measures and invariant packs — reduce
through the bare projection lemmas plus `List.length`, `List.set`, and
a `decide := true` simp config for literal scrutinee conditions, with
`toNat_ofNat_lt` equations stated as haves for omega.  Rollout targets:
the shared 23-argument `vFrame` in `PairFree.Base` serving `Builds`,
`PushTwice`, and `SharedPair`, and the `lFrame`/`cFramePos` frames in
`Iter` and `NegIter`.

## 2026-07-20: A Kernel Unsoundness in Our Own Toolchain

The CollatzLean development
([repository](https://github.com/xrchz/CollatzLean/tree/main/Collatz))
derives `¬ Collatz.Conjecture` through a command elaborator that builds
kernel expressions by hand rather than by tactics.  Aiming that same
machinery at a `Bool`-indexed family whose `false` index is empty derives
`False` with no axioms and no `sorry`, so the development carries no
information about the Collatz conjecture.  A self-contained reproduction,
free of Collatz content, builds on Lean 4.27.0, 4.29.1, 4.31.0, and
4.32.0: our proof gate runs 4.31.0 and is affected.  The defect is
already known to the Lean developers.

Two ingredients combine, and measurement shows each is required.  The
first is `addDecl` with a hand-built `.inductDecl` whose constructor type
carries the projection `orbit.1.1`, reading a `Bool` out of a value whose
constructor holds a `Prop`; the surface elaborator rejects that
projection, and so does the kernel when checking a definition containing
one, yet the inductive declaration path admits it.  The second is a hash
collision: the parity summaries `(fun _stage => false) 78670` and
`(fun _stage => true) 24083` agree on `Expr.hash` and `Expr.approxDepth`,
and replacing them with non-colliding literals makes the kernel reject
the final declaration with "invalid projection".  Hash equality between
structurally distinct terms defeats a check that otherwise fires;
identifying the exact cache requires reading the Lean kernel source,
which this entry does not do.

The demonstration built on top of this — a kernel-checked false claim
about the compiled LEB128 encoder, refuted by running the artifact — was
removed at the user's direction, along with the isolated `Examples`
library that held it.  Its outcome was certain in advance: once the
construction proves `False`, the artifact claim is `False.elim` and the
execution result is what anyone would expect.  The scenario also
overstated the protection, since the execution gate catches a false
theorem only when a test covers the input the theorem misstates.

One correction to the reasoning recorded earlier the same day: replaying
oleans through an independent checker may buy less than claimed, because
the CollatzLean README reports that Nanoda checked the same construction.
Either that report is untested or an independent checker accepts the term
as well, and we do not know which.  Testing a checker against the
reproduction would settle it, and until then the value of adding such a
stage to the proof gate is open.

## 2026-08-01: Machine-Serialized Lean Execution

`tools/leanrun` now owns LeanExe's Lean process boundary.  It selects the root `lean-toolchain` without asking `elan` to download a missing toolchain, sets `LEAN_NUM_THREADS=1`, and enforces the repository's cgroup, priority, I/O, execution-time, and lock-wait limits.  Its default lock is `/tmp/vq-leanrun.<uid>/1`, matching `../vq/tools/leanrun` and preventing simultaneous Lean jobs across the two repositories.

The shared Node process helper routes `lean`, `lake`, `lean-wasm`, `leanc`, `leanchecker`, and `leanmake` through the runner while preserving the original command in diagnostics.  The Talos tools and `check-wat.sh` now invoke the runner directly, so repository-owned compiler, model-generation, proof, execution-test, and WAT-test paths use the same lock.  Active documentation and repository instructions name the runner instead of a hand-written `systemd-run` command.

Shell and JavaScript syntax checks passed for the changed launchers.  `node test/run_process.js` passed its three process-error cases and the new routing checks, and `tools/leanrun true` created the constrained user scope successfully.  Concurrent one-second runner payloads completed in 0.89 and 1.95 seconds, confirming serialization on the shared lock.  `tools/leanrun lean --version` reported Lean 4.31.0 at commit `68218e876d2a38b1985b8590fff244a83c321783`.

## 2026-08-01: PairFree Focused Boundary Under the Shared Runner

`tools/leanrun lake --dir proofs/talos/lean --no-ansi build Project.PairFree.Builds` held the machine-wide Lean slot and reached its 900-second execution limit with status 124 and no diagnostic.  The shared runner excludes concurrent Lean work as the cause, while the verified outer `buildsBody` decomposition and earlier measurements locate the remaining cost inside `buildsPhase2`.  The unchanged target will not run again before a smaller lemma isolates the pair-literal fill loop and its store and read facts.

## 2026-08-01: Stable Runner Command Interface

Interactive timeout overrides formerly required an environment assignment before `tools/leanrun`.  That command shape prevented Codex's approval mechanism from matching the approved runner prefix, causing a new permission request for each duration and target.  The runner now accepts `--timeout`, `--lock-timeout`, and `--toolchain`, and repository instructions keep `tools/leanrun` as the first command token.

The environment variables remain available to repository drivers whose process APIs pass an environment separately.  Shell syntax, missing-option-value handling, invalid lock-timeout handling, and `tools/leanrun --lock-timeout 0 --timeout 10 true` passed.  The last command used the existing runner approval without another permission request.

## 2026-08-01: PairFree Tail Module Boundary

The first division named the post-loop result predicate and moved the post-loop Wasm suffix into `buildsTail`.  That changed the silent 900-second failure into diagnostics in 79 seconds and 83 seconds, revealing a copy-loop measure simplification error and a malformed record update.  Restoring the verified `vMeasure` simplification and correcting the record update removed both errors.

`buildsPhase2` now uses `wp_loop_body_intro`, proving the loop body under a generic postcondition and supplying `buildsTail` as the enclosing block's exit continuation.  `Project.PairFree.BuildTail` gives Lake a module cache boundary between the suffix helpers and the exported construction proof.  A focused build of the new module reached its 300-second limit without a diagnostic, so `buildsTail` still requires a smaller semantic division before another unchanged check.

## 2026-08-01: Binary Validator Soundness

`Project.Artifact.Binary.Validity` defines `CoreValid` independently of the executable validator.  Its judgments cover section order and presence, memory limits, globals, exports, resolved function types, local lookup, every accepted instruction's stack effect, structured-control frames, and function results.  The definition does not characterize validity as successful execution of the validator.

`Project.Artifact.Binary.Proof.Validate` proves soundness from the primitive stack operations through every instruction and the complete module validator.  During that proof, nested `block` and `loop` validation revealed that the executable checker used the enclosing frame base and could consume values below the structured-control entry height; both instructions now use the entry stack height.  The validator also rejects out-of-range instruction constants, matching the signed-width restriction already applied to global initializers.

The soundness module and validator tests pass through `tools/leanrun` without warnings.  New tests reject block and loop bodies that pop below their entry height and reject i32 and i64 constants at the positive signed bound.  One serialized `ValidateFile` process decoded and validated all twenty registered binaries after these changes.

## 2026-08-03: Proof-Kit Entry Tactic PoC

`Project.ProofKit.Control` now provides `wp_entry functionDef as initial'`, which applies the artifact-level `Wasm.TerminatesWith.of_wp_entry` theorem, closes the generated-function lookup with `rfl`, and introduces the initial local frame under a caller-selected name.  The accompanying catalog gives a headless proof agent the import, invocation, and resulting goal boundary.  The first draft exposed two Lean macro-hygiene errors: the module needed to import `CodeLib.Entry` so the theorem name resolved when the macro expanded, and the spliced introduction name needed an explicit `term` category to avoid the `intro match` parser alternative.

The PoC workspace copied the retained prime-factor proof modules, omitted `Source.lean`, and used the repository proof project as a Lake dependency.  The headless invocation selected Pi's existing `openai-codex` credential; Pi then read the catalog, added `Project.ProofKit.Control`, and replaced both entry sequences.  The final diff against `demos/demo-1/proof.lean` consists of one import and two replacements; every theorem statement and later proof step matches the retained proof.

Pi's build and a separate outer run both completed `LeanExeGen.GeneratedRc8c2d9f87deb0758.ArtifactResult`.  A focused compilation of the changed proof built `Behavior` in 12 seconds and `ArtifactResult` in 1.9 seconds on Lean 4.31.0, retaining only the existing linter warnings.  Production use still requires a narrow proof-kit import allowlist, checked catalog injection, and proof-package identity for the imported library sources.

The follow-up `wp_entry_single_call` tactic generalizes the demo's public entry wrapper by accepting its function definition, body declaration, initial-store binder, and `Wasm.wp_call_tw`-compatible callee theorem.  It performs the straight-line entry, call, and return proof using only those arguments and the Talos control-flow rules.  Applied to the retained prime-factor module, it reduced nine mechanical commands to one invocation and rebuilt `Behavior` in 11 seconds and `ArtifactResult` in 1.6 seconds; `demos/demo-1/proof-kit.diff` retains the exact checked transformation.

`leanexegen` now places the proof-kit catalog in each Codex artifact-proof workspace, permits the exact `Project.ProofKit.Control` import, and prompts Codex to use the cataloged entry and single-call tactics when their structural premises match.  Package schema version 2 retains the catalog, while `tool-pins.json` records a digest over the catalog and tactic module.  Independent verification compares the catalog with the checkout, recomputes that digest through the ordinary pin comparison, audits the tactic module, and rebuilds the artifact theorem with the same narrow import allowlist.  The focused Codex protocol and package tests pass.

The first live prime-factor run with this integration stopped at 2026-08-03T20:20:11Z during the formal-specification Codex task.  The authenticated account reported its usage limit exhausted and gave August 7, 2026 at 10:36 PM as the next available time, without a time zone.  The run therefore produced neither a candidate specification nor an artifact and supplies no proof-stage measurement.  The retained baseline for the later comparison remains 238.557 seconds from the start of stage five to the start of stage six.  No alternate model, API key, or manually supplied stage replaced the requested `codex exec` run.

A retry completed all eight stages and independently verified the published package.  Codex imported `Project.ProofKit.Control`, used `wp_entry` for the helper, and used `wp_entry_single_call` for the exported wrapper; the generated proof matches `demos/demo-1/proof-kit.diff` and fell from 329 to 321 lines.  Both runs produced the same 1,348-byte WASM with SHA-256 digest `8ef01d38a73edaca6c9098876af4212bf037ff1a14ba69e186b96a884c54cdcf`, so the proof comparison concerns one exact artifact.  Stage five took 253.925 seconds, 15.368 seconds longer than the 238.557-second baseline, and therefore does not show a generation-time improvement.  The independent verifier completed in 36.6 seconds and accepted `LeanExeGen.GeneratedRc8c2d9f87deb0758.Artifact.artifact_correct`; `demos/demo-1/stdout-with-proof-kit.txt` and `demos/demo-1/stderr-with-proof-kit.txt` retain the generation streams.

## 2026-08-03: Controlled Artifact Reproof

`tools/leanexegen reprove -o <program.wasm> <proof-package>` now reruns only the artifact-proof task.  It validates the input package, requires every tool pin except the proof-kit digest to match the current checkout, and rejects a frozen module that imports the mutable proof kit.  Codex receives the request, formal specification, Program, exact-artifact support, and current catalog, while Source and the old Behavior module remain absent.

The output retains the request, formal specification, Source, WASM bytes, Program, deterministic artifact modules, artifact record, samples, host assumptions, and formal and program task reports.  Publication validates the new package and checks the WASM, artifact record, and each frozen Lean module against the input before installing the result.  Focused JavaScript tests cover argument parsing, proof-library-only pin changes, semantic pin rejection, Source exclusion, frozen-source selection, and proof-kit isolation.

`Project.ProofKit.Control` now provides two structural loop helpers.  `wp_block_loop invariant inv decreasing measure` applies the repeated Talos block and loop rules, while `wp_entry_to_loop functionDef unfolding functionBody as initial'` performs entry conversion, generated-function unfolding, straight-line symbolic execution, and the surrounding block rule before exposing `Wasm.wp_loop_cons`.  Each helper built separately in the retained prime-factor workspace, with the application invariant and measure remaining in the artifact proof.

The controlled run retained the 1,348-byte WASM at SHA-256 `8ef01d38a73edaca6c9098876af4212bf037ff1a14ba69e186b96a884c54cdcf` and preserved every frozen Lean module byte-for-byte.  Codex used `wp_entry_to_loop` and `wp_entry_single_call`, reducing `Behavior.lean` from 321 to 316 lines, and the new package passed independent `leanexegen verify`.  Stage five took 390.849 seconds, 136.924 seconds longer than the preceding 253.925-second proof-kit run, so the evidence supports proof reduction but no time reduction.

## 2026-08-04: Array Proof Generation Baseline

The first accepted proof for the `Array UInt64 → Array UInt64` prime-factor artifact held the specification, source, emitted `Program`, and 1,954-byte WASM fixed at SHA-256 `269a9e58a76bda963617fb1896042781c04beca9d7bb9e15be4ec15bc7a3f23d`.  Stage five took 2,912.341 seconds, and the complete generation run took 3,306.586 seconds.  Independent verification rebuilt and accepted the exact artifact theorem in about 68 seconds.

The accepted 747-line proof used the array representation and control modules, but it derived several stable facts locally.  These included encoded singleton length, input and payload addresses, the 48-byte fixed-array header root, the post-allocation top, unsigned-overflow exclusion, five header subtraction addresses, and the no-growth page comparison.  `Project.ProofKit.Array` now exposes the encoded-size and address facts, while `Project.ProofKit.Allocation.bumpFacts` packages the fixed-array bump facts from the existing-memory bound and WebAssembly page limit.

All four proof-kit modules compile under Lean 4.31.0, and the leanexegen JavaScript tests accept and advertise the allocation module.  A controlled reproof started at `2026-08-04T05:06:11.005Z` with no prior `Behavior.lean`, preserving a from-scratch generation measurement.  The run stopped before its first candidate after the user journal grew from 1.6 GB to 1.7 GB in about four minutes and root free space fell to 1.1 GB; completing a run now requires enough root headroom for the continuing journal output.

## 2026-08-05: Exact-Artifact Proof-Time Reduction

An end-to-end demo-1 run produced a retained 1,938-byte WASM at SHA-256 `dbced77ae7a692ce49e98cb58721cb3c05a3712925e31685c4fd08dba4181be7`.  Stage five ran from `2026-08-05T15:23:01.431Z` to `2026-08-05T16:21:38.206Z`, taking 3,516.775 seconds.  The complete run took 3,958.713 seconds, and an independent verification accepted `LeanExeGen.GeneratedRbade8cb1a4e3a423.Artifact.artifact_correct` in about 51.5 seconds.

The retained baseline proof contains 579 lines and 23,233 bytes.  It uses the array address and encoded-size facts plus `Allocation.bumpFacts`, but it still derives the returned length-word and payload-word address equalities and their `UInt32.toNat` forms locally.  `BumpFacts.wordAddress` and `wordAddress_toNat` now state those general facts for any word that fits within the allocation capacity, and their catalog entry gives the proof agent the exact application form.

A controlled `leanexegen reprove` held the formal specification, Source, WASM, emitted `Program`, artifact-support modules, Codex version, and toolchain fixed while changing the proof kit and guidance.  Stage five ran from `2026-08-05T16:27:07.492Z` to `2026-08-05T16:59:51.622Z`, taking 1,964.130 seconds: 1,552.645 seconds, or 44.15 percent, less than the retained baseline.  The accepted proof contains 591 lines and 22,760 bytes, uses all four new word-address facts, preserves the exact WASM hash, and passed independent verification in about 45 seconds.

One reproof demonstrates that the interface can reduce generation time but does not estimate a stable distribution.  The accepted proof grew by twelve lines while generation became faster, confirming that proof length serves only as a diagnostic measure.  Repeated fixed-artifact runs need internal telemetry for candidate writes, Lean commands, diagnostics, and outer checks before attributing the reduction among model search, proof organization, and elaboration.

[Faster Direct WASM Proof Generation](better-wasm-proving.md) and the [implementation plan](better-wasm-proving-plan.md) record the next structural work.  The plan prioritizes an artifact-derived structural map, split proof checkpoints, complete allocator and array-wrapper theorems, source-derived semantic hints and capsules, and a proof-producing target verification-condition generator.  The `dev` host can add a concurrent Lean-checking lane after installation of Lean 4.31.0 and a semaphore-aware leanexe checkout, while fixed timing comparisons remain on one declared machine profile.

## 2026-08-05: Fixed-Artifact Timing Distributions

The checked demo-1 benchmark now preserves seven complete proof packages over the same 1,938-byte WASM and formal specification.  The unchanged word-address series took 1,964.130, 360.144, and 2,249.443 seconds, yielding a 1,964.130-second median and a 1,889.300-second range.  Its outer-acceptance intervals stayed between 33.573 and 41.742 seconds, while Codex time accounted for the large range.

`tools/leanexegen-telemetry.js` records the stage start, first acceptance, Codex-session interval, outer-acceptance interval, total interval, and accepted source hash.  `tools/leanexegen-benchmark` validates every frozen file, exact artifact identity, semantic tool pin, proof-kit digest, accepted source digest, and recorded measurement before reporting variant distributions.  The mutation test changes a retained request and confirms that the checker rejects the package.

The first timed attempt exposed a machine cache defect before Codex or Lean began: `XDG_CACHE_HOME` resolved through a dangling link to an unavailable disk.  `tools/leanrun` now assigns a repository-local `.lake/cache` by default and accepts `LEANRUN_CACHE_HOME` as an explicit override.  A constrained runner diagnostic confirmed the resulting cache path under the required cgroup.

## 2026-08-05: Complete Fixed-Array Allocator Theorem

`Project.ProofKit.FixedArrayAllocator.region_spec` proves the emitted one-parameter, fourteen-local allocator region from empty-free-list initialization through the no-growth bump path.  Its conclusion includes the six header stores, global 0 and global 2 updates, and returned-root assignment to local 5, parameterized by capacity and stride.  The theorem contains no admitted facts and built under Lean 4.31.0 in 26 seconds with a warm local cache.

An exact demo-1 check extracted instructions 32 through 48 from the frozen singleton branch and proved by reduction that the slice equals `FixedArrayAllocator.region 1`.  The check then instantiated `region_spec` against the exact emitted module with capacity 16 and stride 1.  A remote x86-64 build under `tools/leanrun-dev` also accepted the theorem after populating its cache.

Three fresh fixed-artifact proofs imported `Project.ProofKit.FixedArrayAllocator` and applied `region_spec` at the exact emitted suffix.  They independently verified in 2,556.812, 1,134.008, and 941.494 seconds, producing a 1,134.008-second median and a 1,615.319-second range.  The allocator median is 830.122 seconds, or 42.3 percent, below the unchanged word-address median, while the variance shows that Codex search remains the dominant uncontrolled cost.

## 2026-08-05: Remote Lean Development Lane

The `dev` host now has the pinned x86-64 Lean 4.31.0 toolchain, a source-only checkout at `/mnt/vq/leanexe`, and persistent Talos and Mathlib build caches.  `tools/leanrun-dev` synchronizes source while excluding `.git`, `.lake`, native output, and temporary files, then checks the remote source manifest before execution.  Its preflight also verifies the toolchain, cgroup, semaphore, one-job setting, and remote runner path.

The remote runner enforces a 24-GiB memory limit, zero swap, a sixteen-core quota, and machine-local serialization.  A focused remote build accepted `Project.ProofKit.FixedArrayAllocator`, and `tools/leanrun-dev check` passed after the final source synchronization.  Local timing comparisons remain on the AArch64 benchmark lane because remote and local resource profiles differ.

## 2026-08-05: Singleton Result Region Reduces Median Below 500 Seconds

`Project.ProofKit.FixedArraySingleton.region_result_spec` composes the empty-list allocator with the emitted singleton `Array UInt64` result suffix.  It proves both result stores, their address bounds, the result-local assignments, and `UInt64Array.At` for an arbitrary scalar value, then passes that fact to an arbitrary following program.  Its statement contains no generated namespace, formal specification, source definition, or prime-factor fact.

The exact demo-1 singleton branch reduces after instruction 32 to `FixedArrayAllocator.region 1 ++ FixedArraySingleton.resultSuffix`.  A focused application against the frozen `Program` passed, and replacing the corresponding block in the 618-line allocator proof produced a checked 546-line proof.  The changed block fell from 100 lines to 14, which established that the theorem removes repeated work before timing it.

Three fresh proofs imported `Project.ProofKit.FixedArraySingleton`, applied `region_result_spec`, and passed independent exact-artifact verification.  Stage five took 680.396, 436.403, and 489.993 seconds, producing a 489.993-second median and a 243.993-second range.  The median is 644.015 seconds, or 56.8 percent, below the allocator median and 1,474.137 seconds, or 75.1 percent, below the word-address median.

The three generated proofs contain 530, 532, and 532 lines.  Their Codex intervals were 637.892, 394.336, and 447.849 seconds, while outer acceptance took 32.874, 35.225, and 35.312 seconds.  Demo-1 therefore passes the plan's sub-900-second target, with demo-2 reuse still required to test whether the theorem boundary applies beyond this artifact.

## 2026-08-06: Shared Allocator and Result Proofs

`Project.ProofKit.FixedArrayAllocatorWindow.region_spec` proves the fixed-array allocator for an arbitrary uniform shift of its combined-local operands.  Offset zero covers the fourteen-local Demo 1 wrapper, while offset ten covers Demo 2's twenty-four-local wrapper and assigns the returned root to combined local 15.  Focused builds completed in 15 seconds locally and 20 seconds on `dev` under Lean 4.31.0.

`Project.ProofKit.FixedArrayResult` separates the standard result length and payload stores from application-specific value computation.  Its continuation-generic store theorems accept arbitrary root and scratch local indices, and its representation theorems establish singleton or pair `UInt64Array.At` results from named store transformers.  The module built in 1.0 seconds locally and 2.1 seconds on `dev`.

One frozen-artifact screen passed for each existing demo.  Demo 1 retained the complete singleton theorem and finished stage five in 372.474 seconds, compared with the prior three-run median of 489.993 seconds.  Demo 2 used the offset-ten allocator theorem, both generic payload-store applications, the generic length-store theorem, and `pairStore_at`; its proof fell from 1,639 to 1,430 lines, and stage five fell from 3,260.962 to 1,432.383 seconds while preserving WASM digest `ceb37cd3d61158e7f4162c97cac9b79022518a4e67f895d45a3619c7b5a29712`.

## 2026-08-06: Indexed Input Loader and Tree Baseline

Demo 3 performs lookup in a fixed seven-node binary tree represented by a fifteen-word breadth-first array.  Its 7,186-byte WASM has SHA-256 digest `1a93ec55974666ad54fad73d321b8b9e1f7d67970b272c13bcc77055c8e7631d`, and the accepted direct artifact proof took 2,427.376 seconds.  The 1,398-line proof used the shared shifted allocator and result-store modules, leaving indexed input reads and nested unsigned comparisons as the largest repeated target patterns.

`Project.ProofKit.FixedArrayInput.program_spec` proves the standard indexed input-array loader for an arbitrary in-bounds element and an arbitrary continuation.  The theorem covers the emitted pointer save, encoded index, length load and guard, payload-address calculation, payload load, and local-frame result at any uniform local offset.  `Project.ProofKit.Array.At.generatedElement` packages the exact encoded-index bound and memory-read forms used by Demos 2 and 3, and focused local and remote builds accepted both additions under Lean 4.31.0.

The first fixed-artifact Demo 2 reproof with the indexed loader completed stage five in 573.785 seconds, including 466.634 seconds in Codex and 92.410 seconds in outer acceptance.  The preceding shared-kit screen took 1,432.383 seconds, while the original proof took 3,260.962 seconds, so the indexed-loader run reduced those times by 60.0 percent and 82.4 percent.  The proof grew from 1,430 to 1,493 lines while preserving WASM digest `ceb37cd3d61158e7f4162c97cac9b79022518a4e67f895d45a3619c7b5a29712`, which supplies another case where the semantic boundary improved generation time without reducing source length.

The corresponding Demo 3 indexed-loader reproof took 718.422 seconds, including 591.020 seconds in Codex and 109.383 seconds in outer acceptance.  That result reduced the 2,427.376-second tree baseline by 70.4 percent and reduced the proof from 1,398 to 1,262 lines.  The proof imported `FixedArrayInput`, applied `program_spec`, used `generatedElement`, and preserved WASM digest `1a93ec55974666ad54fad73d321b8b9e1f7d67970b272c13bcc77055c8e7631d`.

`Project.ProofKit.FixedArrayPairResult` extracts the common twenty-four-local pair-return wrapper from the accepted Demo 2 and Demo 3 proofs.  Its constant and indexed-input theorems prove capacity normalization, the offset-ten allocator, input preservation, two result stores, destination assignment, and the returned pair representation without importing a generated or formal-specification module.  Focused builds completed in 6.7 seconds locally and 5.9 seconds on `dev`, while the later composed-continuation additions built in 8.7 seconds locally and 6.7 seconds on `dev`.

The first pair-result screens passed in 512.533 seconds for Demo 2 and 278.656 seconds for Demo 3.  Demo 2 improved by 10.7 percent over its indexed-loader result and fell from 1,493 to 900 lines; Demo 3 improved by 61.2 percent and fell from 1,262 to 672 lines.  Both runs retained their frozen WASM digests and used the shared pair-result theorem at every result branch.

A follow-up prompt made the composed `resultContinuation` the default and caused Demo 2 to reconstruct the entry and lookup traversal one checked segment at a time.  After twenty minutes it had proved the length cases and one of ten lookup nodes, so the run could no longer beat the 512.533-second pair-kit result and was stopped.  The composed theorems remain available when a current continuation already matches, while the default guidance selects `constResultProgram_spec` and `inputResultProgram_spec` without restructuring the branch proof.

`Project.ProofKit.FixedArrayTraversalInput.program_spec` proves the checked indexed loader used by the unrolled search rather than the result wrapper.  It parameterizes the emitter's local-window offset, stores the input pointer and index in combined locals `offset + 5` and `offset + 6`, and leaves the represented element on the operand stack for an arbitrary following comparison.  The module built in 2.4 seconds locally and on `dev`, and its first accepted Demo 2 proof applied the theorem to the query and all ten keys.

That accepted traversal-loader screen took 727.872 seconds, including 669.027 seconds in Codex and 47.359 seconds in outer acceptance.  It reduced the accepted proof from 900 to 804 lines but increased stage-five time by 42.0 percent over the first pair-kit result because Codex constructed an exact nested `program ++ rest` decomposition at every node.  A Demo 3 screen produced no candidate after six minutes and was stopped because it had already exceeded the complete 278.656-second pair-kit time, so the traversal theorem remains available without serving as the default path.

## 2026-08-06: Annotation Vertical Slice

The compiler emits schema-1 JSON sidecars through `lean-wasm compile --annotations`, with `leanexe.call.direct.v1` regions located in the structured instruction tree.  Direct-call discovery covers calls nested under blocks, loops, and both branches, and records immediate local arguments and local results when the emitted sequence exposes them.  The compiler's ordinary and annotated paths produced byte-identical WASM in the focused compatibility check.

The JavaScript consumer validates the schema, artifact length, user-function signatures, complete user-call coverage, structured paths, and exact decoded instruction subsequences.  It maps matched calls to `Wasm.wp_call_tw` and selects `wp_entry_single_call` only for a function containing one top-level decoded call.  Proof-package schema 5 retains the sidecar and recipe plan, while schema 3 and schema 4 packages remain readable without those files.

`tools/leanexegen annotate` recompiled the frozen Demo 1 Source and required exact equality with the retained 1,938-byte WASM before producing a schema-5 package.  The emitted regions matched function 1's call to function 0 and exported function 2's call to function 1 in the frozen Talos Program.  The resulting proof task omitted Source and the compiler, regenerated both call recipes from the frozen sidecar, and independently checked the final artifact theorem.

The annotated Demo 1 reproof completed Stage 5 in 279.110 seconds, consisting of 212.989 seconds in Codex and 42.456 seconds in outer acceptance.  The prior unannotated run took 372.474 seconds, but both runs generated the same 532-line Behavior source with SHA-256 digest `ddce88feccb5b074bf8951189dd5f538ed286201cbe2c0d96d229e61815f38a1`.  Independent verification accepted artifact digest `dbced77ae7a692ce49e98cb58721cb3c05a3712925e31685c4fd08dba4181be7`; repeated trials remain necessary before attributing the 93.364-second difference to annotations.

## 2026-08-06: Complete Fixed-Array Search Annotations

The annotation vertical slice now covers fixed-array length dispatches, saved search-key loads, equality nodes in both operand orders, and key-first unsigned less-than nodes.  The proof kit adds `SearchFrame`, `branchN`, standard pair-result branch composition, and `FixedArrayLtNode.program_spec` with `wp_fixed_array_lt_node`.  The recipe planner orders these regions by structured instruction location, yielding the generated depth-first tree order for Demo 3.

Fresh proof screens did not improve Stage 5 time.  Length recipes reduced Demo 1 from 532 to 517 lines while increasing time from 372.474 to 637.770 seconds, and reduced Demo 2 from 900 to 508 lines while increasing time from 512.533 to 1,387.816 seconds.  Optional search recipes produced a 673-line Demo 3 proof in 392.544 seconds, while a retired partial deterministic starter produced 604 lines in 1,221.892 seconds against the 672-line, 278.656-second reference.

Recompilation with current annotation emission preserved the frozen WASM digests for Demos 1, 2, and 3.  Exact decoded-program matching accepted one length region and two calls in Demo 1, one length region, one key load, and ten equality nodes in Demo 2, and one length region, one key load, seven equality nodes, and three less-than nodes in Demo 3.  Independent verification accepted all three newly annotated packages under `tools/leanrun`.

The cross-demo run found that the search-key recognizer classified Demo 1's ordinary input load from shape alone.  The compiler now requires a matching equality or less-than consumer with the same local window and key local, which removes that region from Demo 1 and retains the intended regions in Demos 2 and 3.  A fresh complete-tree reproof could not start after two attempts because headless Codex reported an account usage limit until August 10, 2026.

## 2026-08-06: Checked Annotation Coordinates

`Project.ProofKit.Annotation` resolves structured block, loop, then-branch, and else-branch paths over a decoded Talos `Program`.  Its `region` function selects the sidecar's exact half-open instruction interval after resolving the nested list.  The module built successfully under Lean 4.31.0 through `tools/leanrun` and is available to generated artifact proofs through the checked proof-kit allowlist.

## 2026-08-06: Checked Pair-Result Regions

The compiler emits `leanexe.array.pair-result.v1` for the complete two-word array-literal assignment and its transfer to the wrapper return local.  Constant results record both words, while indexed results record the represented input index and fixed found flag; both forms retain the destination local and structured branch path.  Demo 2 and Demo 3 each contain twelve matched pair-result regions, while Demo 1 contains none.

Leanexegen generates an artifact-specific `AnnotationMatches` module whose theorems resolve each pair-result interval from the decoded `Program`.  All twenty-four Demo 2 and Demo 3 equalities close by `rfl` against `FixedArrayPairResult.constResultProgram` or `inputResultProgram`, avoiding another allocator-template implementation in JavaScript.  Fresh annotated packages preserved the frozen WASM digests and passed independent artifact verification under the managed Lean runner.

## 2026-08-06: Proving-agent journal

Leanexegen now gives each artifact-proof session a plain `PROOF_JOURNAL.md` file and asks Codex to record its reasoning, Lean results, and changes of direction in prose after each Lean check and significant change in approach.  A successful session must add substantive text, and publication retains the account as `proof-journal.md` under the proof package's existing content index.  Package verification checks its identity and text content, while Lean never imports it or uses it to establish the artifact theorem.

The first live journal trial reproved Demo 2 over the unchanged 7,336-byte artifact with SHA-256 `ceb37cd3d61158e7f4162c97cac9b79022518a4e67f895d45a3619c7b5a29712`.  The accepted proof has 491 lines and took 1,407.477 seconds from Stage 5 start to first acceptance, including 1,340.824 seconds in Codex and 52.009 seconds in the independent outer check; the previous accepted proof had 900 lines and took 512.533 seconds.  The retained journal explains the final length-dispatch, saved-key, equality-node, annotated pair-result, and local-helper structure, but it recorded one initial entry and deferred the remaining account until the complete proof passed.  The prompt now requests updates after every Lean check and significant change in approach, and an independent `tools/leanexegen verify -s` run accepted the published journal-bearing package.

The second live trial used the strengthened prompt and recorded four chronological entries: starter intent, first Lean diagnostics, proof composition, and successful artifact build with dependency audit.  It produced the same 491-line source at the same SHA-256 as the first trial in 365.974 seconds, including 248.742 seconds in Codex and 103.141 seconds in outer acceptance.  This result is 146.559 seconds, or 28.6 percent, below the earlier 512.533-second accepted Demo 2 proof, but the first and second journal trials' identical proof source and 1,041.503-second timing difference show that one pair of runs cannot assign the reduction to journaling.  A separate `tools/leanexegen verify -s` run accepted the second published package.

## 2026-08-06: Journal-derived search composition

Both Demo 2 journals describe three local proof adapters, and their identical accepted `Behavior` source defines those adapters around `FixedArrayEqNode.program_spec`, pair-result programs, and `branchN`.  `SearchFrame.program_spec` and `SearchFrame.keyFirstProgram_spec` now apply either complete equality-node order from the saved frame invariant, while `FixedArraySearch.PairResultContext`, `inputResultProgram_branchN_spec`, and `constResultProgram_branchN_spec` retain the shared runtime facts and compose complete result programs through nested branch continuations.  The catalog, selected strategy guidance, and artifact-proof prompt tell Codex to use these declarations instead of defining another local adapter.

A transformed copy of the accepted Demo 2 proof removed all three local adapters and built successfully against the current proof kit through `tools/leanrun` under Lean 4.31.0.  The proof fell from 491 to 426 lines while retaining the same formal specification, decoded Program, annotation equalities, and artifact theorem.  This focused check establishes applicability and proof reduction; a fresh journaled Codex run remains necessary to measure discovery and proof-generation time.

The first fresh run changed the journal heading's capitalization before its initial Lean check, exposing an exact-heading requirement in package validation.  That requirement constrained the prose format despite the prompt's explicit lack of a prescribed schema and would have rejected the journal after a successful proof.  Validation now accepts any heading and requires substantive non-heading text without NUL bytes; the interrupted proof run stopped before publication and supplied no timing result.

The completed fresh run used `SearchFrame.program_spec`, one `PairResultContext`, ten `inputResultProgram_branchN_spec` applications, and one `constResultProgram_branchN_spec` application without recreating a local adapter.  Its accepted proof has 406 lines and took 512.488 seconds, including 449.555 seconds in Codex and 38.506 seconds in outer acceptance; the earlier 491-line median run took 512.533 seconds, including 440.339 seconds in Codex and 53.587 seconds in outer acceptance.  The journal-derived LTG reduced proof source by 85 lines and changed total time by less than one tenth of a second, supplying discovery and structural evidence without evidence of lower proof-generation time.

The same journal recorded an initial Lake failure before `Behavior.lean`: the starter imported `FixedArrayLtNode` even though Demo 2's checked recipes contain equality comparisons only, and the changed equality dependency made that unused module's compiled archive stale.  The dependent less-than module now has a current Lean 4.31.0 build, and `artifactProofStarter` selects proof-kit imports from the checked recipe modules and their cataloged supporting declarations.  Equality-only artifacts therefore omit `FixedArrayLtNode`, while a less-than recipe retains it for tree proofs.

## 2026-08-06: Demo 3 journal review

The journal-guided Demo 3 reproof preserved the 7,186-byte artifact with SHA-256 digest `1a93ec55974666ad54fad73d321b8b9e1f7d67970b272c13bcc77055c8e7631d` and passed independent package verification.  Its proof uses one `PairResultContext`, the shared `SearchFrame` node theorems, all twelve checked pair-result regions, and all three less-than tactics without a local program adapter.  The accepted source fell from the immediate pair-result reference's 672 lines to 421 lines, while Stage 5 rose from 278.656 to 770.948 seconds, an increase of 492.292 seconds or 176.7 percent.

The journal identifies four failed or avoidable iterations.  The prompt required an edit before the first check, so the agent added three allocator-global facts without evidence that the proof needed them; the first check should expose the starter goal before any edit.  The search-key tactic left a variable number of numeric premises after elaboration, and the less-than tactic postponed an index bound behind its semantic branches, causing two subsequent builds to address the wrong goals.

The search-key tactic now accepts the input representation and index bound through `using`, proves its numeric key-local bounds internally, and presents three frame premises followed by the continuation.  The less-than tactic now accepts the `SearchFrame`, input representation, and index bound through a corresponding `using` form, leaving only its two semantic branches.  A transformed copy of the accepted Demo 3 proof uses these forms, falls to 403 lines, and builds both `Behavior` and `ArtifactResult` against the current proof kit under Lean 4.31.0.

The journal also records about seven minutes spent mapping the complete tree before the agent wrote its first proof body.  The annotations already contain the ordered equality, less-than, and pair-result regions, but the proof task still makes the agent reconstruct their parent-child continuation graph in Lean.  The next LTG experiment should generate a checked artifact-specific tree composition theorem or proof skeleton from that graph, leaving the agent the formal-specification equations at the successful and missing leaves.

## 2026-08-06: Fixed search-tree composition

`Project.ProofKit.FixedArraySearchTree` defines a generic tree whose branches contain key-first equality and unsigned less-than nodes and whose leaves contain standard found and missing pair results.  `Tree.program_spec` proves the complete artifact fragment by induction from one search frame, one pair-result context, fixed index and destination bounds, and one equation between the public result and `Tree.result`.  The module imports no generated program or formal specification and built in 1.8 seconds under Lean 4.31.0.

A seven-node descriptor is definitionally equal to Demo 3's frozen search program after the checked key load.  Replacing the journaled node-by-node proof with one `Tree.program_spec` application reduced the active `Behavior` source from 421 to 155 lines, and the transformed package built through `ArtifactResult`.  A new Codex timing result remains pending.

The annotation consumer now derives a complete `Tree.branch` and `Tree.leaf` descriptor from the checked equality, less-than, and pair-result paths.  It emits the descriptor and an `rfl` region equality in `AnnotationMatches`, records both names and `Tree.program_spec` in the proof plan's composition list, and imports the tree module into the proving task.  The generated Demo 3 equality and transformed `ArtifactResult` both built successfully, leaving a fresh Codex reproof to measure whether the 266-line reduction and eliminated graph search reduce Stage 5 time.

## 2026-08-07: Search-tree composition screen

Three fresh composition runs preserved Demo 3's 7,186-byte artifact and SHA-256 digest `1a93ec55974666ad54fad73d321b8b9e1f7d67970b272c13bcc77055c8e7631d`.  Their Stage 5 times were 405.385, 326.320, and 303.478 seconds, giving a 326.320-second median and a 101.907-second range.  The median run used 292.154 seconds in Codex and 26.238 seconds in outer acceptance, and a separate `tools/leanexegen verify -s` run accepted the first published package.

The preceding journal-guided node proof took 770.948 seconds and 421 lines, so the complete composition reduced the median by 444.627 seconds, or 57.7 percent, and 277 lines, or 65.8 percent.  The 278.656-second pair-result reference remains 47.664 seconds below the new median despite containing 672 lines, while the fastest composition run was 24.821 seconds above that reference.  The composition median is 66.224 seconds below the 392.544-second optional-search screen, but the spread among Demo 3 runs prevents attribution of every timing difference to the proof method.

All three journals record the intended proof process.  Each agent ran the starter check before editing, selected the complete composition before node tactics, and produced the same 144-line source with SHA-256 digest `edde0a3f19777c1a7cdc8a35654344d474cf995f30cbfa31ac1becd1b62a0a14`.  Each first build after the single proof edit succeeded without node-level expansion or allocator arithmetic, providing direct evidence that the generated descriptor removed graph-reconstruction and Lean-iteration failures.

## 2026-08-07: Journal-derived search wrapper

The three complete-tree journals produced byte-identical proof sources and repeated the same length dispatch, invalid result, query load, search-frame construction, and return continuation.  `FixedArrayEqNode.keyFrame_searchFrame` now constructs the post-load invariant, while `FixedArraySearchTree.Tree.wrapperProgram_spec` composes those wrapper regions with `Tree.program_spec`.  The theorem imports no generated program or formal specification and leaves the invalid-result equation, `Tree.Valid`, and the formal-result equation as its application-specific premises.

The recipe planner recognizes this wrapper only when the normalized inequality dispatch occupies the function prefix, its invalid branch consists of the annotated zero pair, its valid branch consists of the annotated query load followed by the complete tree, and the function ends with local 14.  It records those numeric parameters as a version-two composition, and `artifactProofStarter` applies the wrapper theorem before Codex begins.  Node tests pass, the generic module builds under Lean 4.31.0, and a seventy-line Demo 3 proof built through `ArtifactResult`, compared with 144 lines for each preceding generated composition proof; a fresh Codex timing result remains pending.

The first fresh version-two run completed Stage 5 in 253.644 seconds, including 215.383 seconds in Codex and 29.284 seconds in outer acceptance.  It produced a 76-line proof, preserved the 7,186-byte artifact and SHA-256 `1a93ec55974666ad54fad73d321b8b9e1f7d67970b272c13bcc77055c8e7631d`, and passed independent package verification.  This result is 72.676 seconds below the 326.320-second preceding composition median and 25.012 seconds below the 278.656-second historical pair-result result, but one run does not establish either reduction as repeatable.

The proving journal records an avoidable intermediate failure.  Codex removed the three explicit semantic holes from the wrapper theorem application while adding their bullets, which left implicit numeric parameters unresolved; restoring the holes made the proof build.  The same three simplification proofs are determined by the generated expected-result definition and descriptor, so the next starter iteration should supply them and retain explicit wrapper parameters, leaving Codex to check the complete candidate and report any mismatch.

The specialized starter now names all six wrapper parameters and supplies the three checked simplification proofs.  Its import set contains only the generated formal specification, Program, annotation equalities, and `FixedArraySearchTree`, eliminating the import cleanup performed by the first agent.  A focused copy built through `ArtifactResult`, and the prompt now tells Codex to preserve a candidate whose initial build succeeds and to finish only the journal and required final check.

Three fresh complete-starter runs finished Stage 5 in 109.607, 121.976, and 131.413 seconds, giving a 121.976-second median and a 21.806-second range.  Every initial build passed, Codex made no proof edit, and each published proof contained the same 77 lines with SHA-256 `18c1d84f94723f6db76d5ad701c951472fcc80c5c76acade4d91f558d9f4ee2a`; independent verification accepted the first package.  The median is 204.344 seconds below the preceding complete-tree median and 156.680 seconds below the historical 278.656-second pair-result result.

## 2026-08-07: Fixed search-chain composition

The Demo 2 journals describe ten loaded-first equality nodes with a found pair at each equal branch and one missing pair after the last unequal branch.  `FixedArraySearchChain.Chain` represents that first-match graph with `next` and `last`, while `Chain.program_spec` proves its decoded program by induction.  `FixedArraySearch.wrapperProgram_spec` now contains the fixed-length dispatch, invalid result, query load, and public return shared by the chain and tree wrapper theorems.

The annotation consumer reconstructs a chain from exact nested branch paths and emits a checked descriptor equality.  Complete coverage of the function prefix, both length branches, the saved-key load, the chain, and final local read produces a version-two composition and complete semantic starter.  The generic chain module builds under Lean 4.31.0, JavaScript tests pass, and the current Demo 2 annotations produce one ten-node wrapper composition; a fresh proof-time result remains pending.

The first fresh run stopped before checking `Behavior`: elaborating the ten-node descriptor equality in generated `AnnotationMatches` exceeded Lean's default recursion depth.  The behavior starter already used the required higher limit, so the generator now applies `maxRecDepth 1048576` to the annotation module as well.  This changes only elaboration resources for the checked equality; the descriptor, decoded Program, formal specification, and artifact bytes remain unchanged.

Three corrected Demo 2 chain runs finished Stage 5 in 110.332, 110.165, and 110.711 seconds, giving a 110.332-second median and a 0.547-second range.  Every initial build succeeded, Codex made no proof edit, and each package contained the same 76-line proof with SHA-256 `7f47dc8d68291f4e3c08b565478119cfa1b33f230cb4a0ffc572a8cc08f60f2c`; independent verification accepted the first package.  The median is 402.156 seconds, or 78.5 percent, below the 512.488-second journal-derived reference, while the proof fell by 330 lines, or 81.3 percent.

All three journals report a second in-session build after the initial starter build passed, although Codex made no candidate edit.  The prompt now tells Codex to return after recording that initial success, while the orchestrator's existing outer-acceptance phase rebuilds the unchanged proof independently.  A candidate edit still requires the prescribed final in-session build before return.

Three subsequent Demo 2 runs under the single-check prompt took 107.144, 114.390, and 124.539 seconds, for a 114.390-second median and a 17.395-second range.  Their Codex sessions took 66.295, 66.515, and 76.147 seconds, and their outer-acceptance checks took 31.673, 36.550, and 36.267 seconds.  Each run retained the same accepted proof source, and its journal confirms one successful in-session check with no edit, but the median total increased by 4.058 seconds over the preceding 110.332-second result; the removed incremental check was not a material part of the measured total.

## 2026-08-07: Held-out bounded-map baseline

Demo 4 fixes `input.map (fun element => element + 1)` for arrays of at most eight words and returns an empty array for longer inputs.  The generated 1,913-byte WASM artifact has SHA-256 digest `c538d40936b426ba875b3dae1913e62ff00a44b34adff2adcd70922e5a4c95ff`; its one reachable function contains 456 instructions, 16 locals, and three loops.  The preexisting compiler annotations reported no region, and the proof planner supplied no recipe or composition.

The held-out proof took 2,364.735 seconds from Stage 5 start to first acceptance, with 2,255.687 seconds in Codex and 98.593 seconds in outer acceptance.  Codex produced a 457-line proof at SHA-256 `6bd050aab0f4e1124e9ed2a2ef6e75a6020e7ab7b90ce82d2315dc0668b08488` after 27 journaled edited checks.  Independent acceptance proved the final embedded-byte theorem, and sample execution checked wrapping addition and the overlength empty result.

The journal separates the proof cost into bounded-length dispatch, dynamic capacity normalization, an allocator region with unused trailing locals, a dynamic result-length store, the transformed-prefix map loop, and final empty-array construction.  The valid branch reused `FixedArrayAllocatorWindow.region_spec` at offset two, while the invalid branch proved the same allocator directly because its offset-zero window sat inside a 16-local frame.  The first LTG iteration will generalize those boundaries before deriving a complete map-wrapper composition.

## 2026-08-07: General allocator-window theorem

`Project.ProofKit.FixedArrayAllocatorWindow.region_spec_withTail` accepts an explicit count of unused locals following the allocator scratch window.  The existing `region_spec` theorem remains as the tail-zero specialization, preserving current callers.  Focused builds accepted the generalized module and `Project.ProofKit.FixedArrayPairResult` under Lean 4.31.0.

The controlled Demo 4 reproof used the new theorem for the offset-zero allocator in a sixteen-local frame.  Stage 5 completed in 1,191.695 seconds, compared with the 2,364.735-second held-out baseline, and the journaled edit count fell from 27 to 19.  The specification, source, WASM bytes, decoded Program, and artifact theorem remained fixed.

The journal assigns the remaining cost to bounded unsigned length dispatch, generated capacity arithmetic, and the map loop's prefix invariant.  The next proof-kit increment will represent these as compiler-template theorems and add exact artifact-checked annotations and recipes.  Demo 4 will receive another controlled reproof before the earlier demos receive compatibility checks.

## 2026-08-07: Bounded-length annotation and theorem

`FixedArrayLengthDispatch.leProgram_spec` proves the eight-instruction unsigned upper-bound prefix and leaves semantic valid and invalid size cases.  `wp_fixed_array_length_le_dispatch` selects that theorem from an exact current program suffix.  The module builds under Lean 4.31.0.

The compiler recognizes the corresponding IR condition and emits a `le-unsigned-v1` fixed-array length-dispatch region.  The consumer checks the decoded `leUI64` prefix, branch roles, and bound before selecting the new theorem and tactic.  Node tests cover the direct upper-bound form alongside both existing normalized encodings.

`tools/leanexegen annotate` recompiled the frozen Demo 4 source, reproduced the artifact digest, and produced the checked invocation `wp_fixed_array_length_le_dispatch 5, 8`.  The region covers top-level instruction indices zero through eight and records the valid then branch and invalid else branch.  This annotation removes the entry-dispatch discovery work from the next controlled proof session.

## 2026-08-07: Complete bounded-map theorem

`Project.ProofKit.FixedArrayMapAdd.wrapperProgram_spec` proves the compiler's canonical bounded `Array UInt64` wrapping-add map for arbitrary maximum size and addend.  The proof composes `FixedArrayLengthDispatch.leProgram_spec` and `FixedArrayAllocatorWindow.region_spec_withTail`, then discharges the capacity expression, dynamic result length, prefix-preserving map loop, wrapping payload writes, and empty-array branch.  A focused Lean 4.31.0 build completed without warnings.

The compiler now recognizes the exact extracted IR form containing the upper-bound condition, one-word `arrayMapSlots` addition, empty array literal, canonical result locals, one input, and one result.  It emits `leanexe.array.map-add.v1` over the complete top-level function, and the consumer selects `FixedArrayMapAdd.wrapperProgram_spec` only after generating a Lean-checked equality over the decoded artifact region.  Reannotating the frozen Demo 4 package reproduced the same 1,913-byte artifact digest and generated the equality `func0 = FixedArrayMapAdd.wrapperProgram 8 1` after region normalization.

The deterministic artifact starter reduces the public theorem to the checked wrapper theorem and the existing `RuntimeReady` facts.  Its focused diagnostic copy compiled in 2.5 seconds after the generated specification, decoded Program, and annotation module were available.  The JavaScript protocol tests, compiler build, proof-kit build, byte-identity annotation, generated region equality, and diagnostic behavior proof pass.

The controlled reproof accepted the unchanged 66-line starter on its first Lean check.  Stage 5 took 103.123 seconds, comprising 66.734 seconds in Codex, 27.688 seconds in outer acceptance, and the remaining orchestration time; the held-out baseline took 2,364.735 seconds and the allocator-window iteration took 1,191.695 seconds.  The final package retained WASM digest `c538d40936b426ba875b3dae1913e62ff00a44b34adff2adcd70922e5a4c95ff`, recorded proof-source digest `bf07793985539b6c0a7e9076c97f836050c859b47b13ab3f70a3383270b29d56`, and passed an independent `leanexegen verify` run.

The compatibility checks retained every deterministic result.  `node test/leanexegen.js` passed the annotation, recipe, starter, package, and publication tests, while `tools/talos-proof.js check --all` regenerated the checked artifacts and built all 20 completed Talos cases through the 3,335-job aggregate target.  Existing linter warnings in older proofs remain unchanged.

A fresh Demo 1 headless reproof from its older pair-result package produced no accepted proof or Lean diagnostic within fifteen minutes, so the screen was stopped and contributes a timeout-censored observation rather than a compatibility result.  Its duration exceeded both the 372.474-second historical baseline and the 637.770-second length-recipe result, indicating agent search unrelated to the new map recognizer.  The map recognizer requires the exact bounded `arrayMapSlots` IR form, and the JavaScript tests, aggregate proof build, and byte-identity Demo 4 run provide the deterministic compatibility evidence for this increment.

## 2026-08-07: Exact-artifact verification paper

The `paper` directory contains an eighteen-page LaTeX research-paper draft, a thirty-two-entry cited bibliography, a rendered PDF, build instructions, and a three-pass review record.  The paper describes the exact-byte theorem chain, `leanexegen` orchestration, checked annotations and proof recipes, four proof-generation cases, trust boundaries, related systems, and the roadmap toward broader profiles and optional source-theorem transport.  Its comparison covers mechanized WebAssembly semantics, program logics, verified compilation, translation validation, proof-carrying code, native-code checking, and machine-assisted Lean proving.

The technical review checked claims against the artifact registry, draft release record, representative exact-artifact declarations, decoder and validator soundness modules, `leanexegen` implementation, conformance evidence, and retained demo histories.  It records that release revision `febed96d02f7654a522fc15dc0e6e256f95a782a` lacks its cold-checkout receipt, while the manuscript and Demo 4 results postdate that record.  It also states the Talos imported-memory defect, Lean 4.31.0 kernel qualification, missing experimental model and hardware metadata, absence of source-theorem transport, and the operational rather than proved information isolation between agent tasks.

The final BibTeX and two-pass LaTeX build produced `paper/main.pdf` with no undefined citations, undefined references, overfull boxes, or BibTeX warnings.  Text extraction and rendered-image inspection covered the title page, evaluation tables, trust section, related-work comparison table, and reproduction record.  The PDF has eighteen US Letter pages, 253,975 bytes, and SHA-256 digest `434179c6cc5661ee4f1e0848a9cf6f396445a9dfa583956a65c1ff8f00e4b7d6`.

## 2026-08-07: Bounded-map timing distribution

Two additional fixed-artifact Demo 4 reproofs completed Stage 5 in 144.173 and 109.165 seconds.  Together with the first 103.123-second run, they give a 109.165-second median and a 41.050-second range.  Codex time has a 69.549-second median and a 14.074-second range, while independent outer acceptance has a 28.272-second median and a 2.924-second range.

Every run preserved the 1,913-byte WASM digest `c538d40936b426ba875b3dae1913e62ff00a44b34adff2adcd70922e5a4c95ff` and the 66-line proof digest `bf07793985539b6c0a7e9076c97f836050c859b47b13ab3f70a3383270b29d56`.  Each journal records one successful initial Lean check, no proof edit, and no repeated in-session check.  Separate `leanexegen verify` runs accepted the second and third packages, completing independent verification of the three-run series.

The final configuration reduces median Stage 5 time by 95.4 percent from the 2,364.735-second held-out baseline and by 90.8 percent from the 1,191.695-second allocator-only iteration.  This satisfies the three-run promotion rule for the bounded-map theorem, annotation, recipe, and deterministic starter.  The next experiment requires an out-of-sample loop whose semantic structure differs from fixed-output-length map, with bounded filter providing a variable-output-length candidate already supported by the compiler.

## 2026-08-07: Scalar-loop annotation boundary

The remaining Demo 1 proof spends its substantive work on function zero's scalar trial-division loop.  Its array wrapper, allocation, result stores, and call boundaries already use shared theorems, while the helper proof still defines the generated frame, invariant, measure, mathematical transition lemmas, and each instruction branch.  The three fixed-array wrappers and the bounded filter now finish near the 90-to-122-second agent and acceptance floor, making this scalar loop the next measured boundary.

The compiler now emits `leanexe.loop.while.v1` for extracted `Stmt.while` regions and `leanexe.loop.fold.v1` for top-level multi-accumulator loop folds.  The while sidecar records the IR guard, complete IR body statement, scratch-local start, structured location, continuation, and generator chain, while the loop-fold form records accumulator, staging, done, release, and result details.  The JavaScript consumer checks the reported block, nested loop, exit branch, back edge, and fold-specific copies against the frozen decoded Program before selecting the generic loop recipe.

`tools/leanexegen annotate` recompiled Demo 1's frozen source to the existing 1,938-byte artifact with SHA-256 digest `dbced77ae7a692ce49e98cb58721cb3c05a3712925e31685c4fd08dba4181be7`.  Function zero contains one ordinary while region at top-level interval two through three, with scratch locals beginning at 18 and a complete transition statement for the small-result, prime-result, division, and divisor-advance branches.  The compiler build, protocol tests, corrupt-annotation tests, byte-identity check, and recipe generation pass; the next controlled reproof will measure whether this source-free transition map reduces Stage 5 time.

The first reproof completed Stage 5 in 276.795 seconds and passed independent verification, but the proving journal states that Codex found the retained singleton-3 proof elsewhere in the repository.  Its 532-line source has the same `ddce88feccb5b074bf8951189dd5f538ed286201cbe2c0d96d229e61815f38a1` digest as that package.  The result therefore measures retrieval of an exact artifact-specific proof and is excluded from the annotation comparison.

The proof prompt now prohibits reading demos, benchmark packages, archived proofs, or another generated namespace outside the task workspace.  It still permits reading dependency source needed to confirm declarations in the supplied catalog and strategy guide, preserving access to generic LTG.  A replacement run must satisfy this isolation rule before its telemetry can enter the fixed-artifact series.

The isolated replacement produced no accepted proof or Lean diagnostic in approximately 1,082 seconds, and the owned Codex process was then interrupted.  The censored duration exceeds the slowest retained singleton run of 680.396 seconds and the plan's 900-second scalar-loop threshold.  Annotation prose alone therefore fails the promotion rule, so this configuration will not receive two repeat trials.

The next proof-time boundary is a checked scalar transition composition.  Its generic descriptor must cover the expression and statement forms used by scalar loops, and its theorem must prove the corresponding Talos weakest-precondition transition while remaining parameterized over the application invariant and measure.  Generated annotation support will tie an exact decoded loop body to that descriptor by `rfl`, removing branch-shape and local-update reconstruction from the Codex session without adding a program-specific theorem to the shared proof kit.

## 2026-08-07: Checked scalar transitions

`Project.ProofKit.ScalarTransition` defines typed scalar expressions and statements, their state evaluator, and the exact Talos instruction program for each descriptor.  The expression language covers the scalar operations emitted by the compiler, including its guarded unsigned division and remainder sequences with two scratch locals.  The statement language composes assignments, sequences, and conditional branches without referring to a generated artifact or application specification.

`Expr.program_spec` proves weakest-precondition composition for every expression and arbitrary following program, postcondition, operand-stack tail, store, and host environment.  `Stmt.program_spec` lifts the result through statement structure, while `Expr.eval_preserves_below` proves preservation below the descriptor's scratch window.  A focused Lean 4.31.0 build completed the 2,981-job target without warnings through `tools/leanrun`.

`whileProgram_spec` now composes a block-wrapped while loop from the checked condition and body transitions.  The theorem accepts an artifact-defined invariant and natural-number measure, proves every exit and back-edge instruction, and leaves the invariant, decrease, and terminal postcondition mathematics to the caller.  Its focused Lean 4.31.0 build completed without warnings through `tools/leanrun`.

The checked theorems do not yet connect a Demo 1 annotation to its decoded loop body.  The next increment will reify the supported compiler IR into the neutral descriptor and prove exact agreement with the compiler emitter.  The generated artifact package will independently check descriptor-program equality against the decoded WASM before applying the neutral loop theorem.

## 2026-08-07: Compiler-certified scalar descriptors

`LeanExe.Wasm.ScalarDescriptor` defines total reification and instruction emission for the scalar IR subset used by Demo 1's trial-division loop.  The production emitter selects this path after successful reification and retains its former partial implementation as the fallback for unsupported syntax.  `LeanExe.Wasm.ScalarCertificate` proves agreement for reified expressions, conditions, statements, and block-wrapped while loops.

Version-one while annotations now contain the structured descriptor beside the existing diagnostic renderings.  The consumer validates its complete recursive schema, generates neutral `Project.ProofKit.ScalarTransition` declarations, and proves exact equality between the descriptor program and the frozen decoded region.  The proof recipe names that equality, the generated program, and `whileProgram_spec`, while annotations without a reifiable descriptor retain the existing control-flow recipe.

The compiler and proof-kit focused builds passed under Lean 4.31.0, and `node test/leanexegen.js` accepted the malformed-descriptor and unsupported-version tests.  A direct check recompiled the original 1,348-byte scalar walkthrough to digest `8ef01d38a73edaca6c9098876af4212bf037ff1a14ba69e186b96a884c54cdcf`, generated its Talos model, and built the resulting descriptor-region equality.  That check also confirmed that the emitter refactoring preserved every byte of the retained artifact.

The production `tools/leanexegen annotate` workflow then recompiled the current array-wrapper Demo 1 to its retained 1,938-byte artifact with digest `dbced77ae7a692ce49e98cb58721cb3c05a3712925e31685c4fd08dba4181be7`.  It generated the function-zero scalar descriptor, built the exact top-level interval equality, validated the proof recipe, and created a source-free annotated package.  `tools/leanexegen verify` completed independent verification of that package.

This increment removes instruction-shape and local-update reconstruction from the next Demo 1 proving session.  The remaining goals concern the prime-factor invariant, descriptor-level state equations, measure decrease, and the terminal mathematical result.  Fixed-artifact timing trials remain necessary before the scalar bridge earns promotion, followed by a held-out loop with different arithmetic and invariant structure.

The emitter compatibility gates passed after the descriptor path became the production scalar emitter.  The evidence includes 791 accepted execution cases, 45 expected rejections, 14 expected traps, 340 standard-Lean comparisons, 62 IR-interpreter comparisons, the focused runtime and ABI suites, nine WAT-to-binary byte comparisons, and all twenty registered Talos proof cases.  Existing linter warnings in older Talos modules remain unchanged.

`node test/run_all.js` stopped before its compiler tests because `proofs/artifacts/release.json` records the preceding proof-kit input digest.  The focused tests and every later command in that driver were run directly, while the draft release record remained unchanged during development.  A future release-record update must bind a committed source revision and the final proof-kit inputs rather than record this intermediate tree.

The first scalar-descriptor timing trial stopped during job setup before Codex received the proof task.  Every retained Demo 1 timing package records `codex-cli 0.146.0`, while the installed command now reports `codex-cli 0.147.0`; `leanexegen reprove` rejects that identity change.  A valid comparison requires either the recorded 0.146.0 executable or a new baseline and descriptor series under 0.147.0.

`leanexegen reprove --new-codex-series` now starts the latter series explicitly.  Stage-report schema two records separate Codex identities for the preserved formal specification, preserved Lean program, and replacement artifact proof, avoiding a false attribution of the earlier tasks to the new executable.  An ordinary reproof still requires the recorded artifact-proof identity, while the new-series option rejects use when no identity change exists.

## 2026-08-08: First scalar-descriptor timing result

The matched Codex 0.147.0 baseline completed Stage 5 in 2,017.931 seconds, including 1,953.883 seconds in Codex and 57.008 seconds in outer acceptance.  The scalar-descriptor trial preserved the formal specification, Lean source, 1,938-byte WASM digest, proof kit, semantic tool pins, and task limits, then completed in 3,692.913 seconds, including 3,565.493 seconds in Codex and 112.292 seconds in outer acceptance.  Independent `leanexegen verify` runs accepted both packages.

The annotated trial increased total proof time by 1,674.982 seconds, or 83.0 percent.  Its 704-line accepted proof uses `AnnotationMatches.function_0_while_loop_0_eq` and `ScalarTransition.whileProgram_spec`, compared with 734 lines in the baseline, but the package also contains length-dispatch and direct-call recipes.  The journal records 79 entries rather than 65 and identifies repeated work on the wrapper dispatch frame as well as descriptor-evaluator equalities, scratch-local updates, and conversions between `ScalarTransition.State` and the exact WASM local frame.

This pair measures the complete current annotation package and does not isolate the scalar theorem.  The next controlled input will retain only `function-0.while-loop-0`, excluding wrapper and call recipes before recipe and starter generation, while preserving the same frozen artifact and proof kit.  The retained baseline and full-annotation packages now reside under `benchmarks/leanexegen/demo1-array` so another machine failure cannot erase this evidence.

`LeanExe.Wasm.ScalarDescriptor` now computes expression and condition reads, statement reads and explicit writes, and scratch width for every reified scalar descriptor.  `Project.ProofKit.ScalarTransition` implements the corresponding neutral analyses and proves `Stmt.eval_preserves_below`: statement evaluation preserves any combined local below the scratch boundary that does not occur in the computed write set.  The compiler module and 2,981-job proof-kit target build under Lean 4.31.0, while the annotation protocol test confirms that the scalar-loop recipe makes the theorem available to Codex.

`leanexegen annotate --only-region` validates the complete compiler sidecar before retaining selected semantic regions and the direct-call regions required for decoded-call coverage.  A calls-only Demo 1 control contains `function-1.direct-call-0` and `function-2.direct-call-0`, while its matched candidate adds only `function-0.while-loop-0`; neither package contains the length-dispatch recipe that confounded the first comparison.  Both packages reproduce the 1,938-byte artifact digest and pass independent `leanexegen verify` runs under the current proof-kit identity.

The first calls-only proof session ran for approximately sixty-five minutes before outer acceptance rejected its direct import of unsupported module `Project.Common`.  Its ordinary Lean build had accepted that import because the dependency exists in the proof project, so the failure reveals a gap between the task's prescribed check and the publication allowlist rather than an artifact-proof diagnostic.  Artifact-proof workspaces now include `PROOF_IMPORT_CHECK.js`, generated from the same allowlist as outer acceptance, and the task runs it before each Lean build; unit tests accept `Project.ProofKit.Control` and reject `Project.Common`.

## 2026-08-08: Isolated scalar-descriptor result

The corrected calls-only control completed Stage 5 in 2,645.818 seconds, including 2,558.659 seconds in Codex and 75.772 seconds in outer acceptance.  The matched candidate added only `function-0.while-loop-0` and completed in 3,894.697 seconds, including 3,811.538 seconds in Codex and 73.440 seconds in outer acceptance.  Both packages preserve the 1,938-byte artifact digest `dbced77ae7a692ce49e98cb58721cb3c05a3712925e31685c4fd08dba4181be7` and passed independent verification.

The candidate regressed total proving time by 1,248.879 seconds, or 47.202 percent, and therefore receives no repeat trials.  Its accepted proof applies the generated descriptor equality and `ScalarTransition.whileProgram_spec`, reduces source from 722 to 674 lines and from 3,418 to 3,257 whitespace-delimited words, and does not use `Stmt.eval_preserves_below`.  The structural reduction remains secondary evidence, while raw source bytes and identifier length do not measure proof complexity.

The calls-only journal shows that Codex reconstructed the neutral descriptor during its first few edited checks.  Both journals then concentrate on the trial-division invariant, descriptor evaluator cases, local-index and `UInt64` conversions, and the public singleton wrapper; the candidate also records explicit allocator-frame inference work.  The next experiment will supply checked fixed-frame transition equations that summarize scratch staging and will use a shared singleton-wrapper composition in both configurations to remove unrelated wrapper variance.

The host wall clock changed during both runs, making their UTC timestamp differences inconsistent with elapsed process time.  `proof-telemetry.json` measures `totalMilliseconds`, `codexSessionMilliseconds`, and `outerAcceptanceMilliseconds` with `process.hrtime.bigint`, and those monotonic values govern the comparison.  The retained benchmark documentation records the discontinuity so later tooling does not derive elapsed time from the ISO fields.

## 2026-08-08: Journal-guided proof iteration

Every proof-time loop now reviews the journal, accepted proof, and telemetry together before selecting an annotation, LTG, or instruction change.  The repository instructions record proving time as the primary metric and accepted proof structure as secondary evidence, while requiring held-out cases and preservation of failures.  Raw source bytes and identifier length have no negative weight because shared theorem use can introduce longer declaration names while reducing proof structure.

The artifact-proof prompt now asks the agent to name each supplied recipe, theorem, tactic, and annotation it tried, describe its effect or reason for abandonment, and identify missing general assistance suggested by diagnostics.  It also permits the agent to abandon a direct recipe whose shape does not match or whose residual goals are worse, without restructuring unrelated code solely to force the application.  `node test/leanexegen.js` passes with assertions covering these instructions.

## 2026-08-08: Complete singleton-wrapper composition

`Project.ProofKit.FixedArraySingletonWrapper.wrapperProgram_spec` proves the complete one-parameter singleton-array entry program around an arbitrary store-preserving scalar callee.  Its proof covers length dispatch, the invalid pass-through branch, checked first-element loading, scalar-call composition, capacity calculation, fixed-array allocation, singleton stores, and public return.  A focused Lean 4.31.0 build completed the 3,014-job module target in 3.9 seconds.

The annotation consumer recognizes the canonical one-parameter, fourteen-local entry layout and emits a complete composition before region-level recipes.  Its generated `AnnotationMatches` declaration states that the exact decoded entry function equals `FixedArraySingletonWrapper.wrapperProgram callee`, and Lean checks that equality by reduction.  `tools/leanexegen annotate` preserved Demo 1's 1,938-byte artifact digest `dbced77ae7a692ce49e98cb58721cb3c05a3712925e31685c4fd08dba4181be7` and built the equality successfully.

The deterministic proof starter now reaches the complete wrapper boundary and leaves the scalar callee theorem and formal-result equations to the proving agent.  `node test/leanexegen.js` validates the recipe identity, proof-kit import, generated source, starter selection, and rejection of a changed result-local assignment.  A matched timing screen remains necessary, and both scalar configurations must receive this wrapper composition so the next comparison measures fixed-frame transition assistance rather than entry-proof variance.

## 2026-08-08: Checked compact scalar transitions

`Project.ProofKit.ScalarTransitionU64` defines a compact scalar state, condition and statement evaluators, and generic correspondence theorems to `ScalarTransition.State`.  The correspondence proof applies to every supported descriptor expression and statement, including short-circuit conditions and scratch-staged unsigned division or remainder.  Two zero-or-one comparison facts support the Boolean word normalization emitted by the compiler.

The annotation consumer symbolically evaluates each checked descriptor and emits named condition and body transitions over the complete fixed local frame.  Constant propagation reduced Demo 1's generated body from the compiler's nested Boolean encodings to five semantic branches, and each proof branch supplies its path conditions to a restricted simplifier set.  The production annotation command preserved artifact digest `dbced77ae7a692ce49e98cb58721cb3c05a3712925e31685c4fd08dba4181be7`, built the generated equations, and passed independent package verification.

The next matched reproof will compare the checked transition equations against the retained scalar-loop configuration while giving both sides the complete singleton-wrapper composition.  Proving time remains the primary metric, while accepted proof structure records repeated evaluator reductions, local scaffolding, and shared theorem use.  Raw bytes, word length, and identifier length carry no penalty because longer declaration names can identify effective reuse.

## 2026-08-08: Matched compact-transition result

The first candidate session completed its Lean artifact proof but failed publication because the chosen WASM basename mapped back to the existing input proof-package path.  A second candidate used a distinct result basename and published successfully.  Initial generation and `reprove` now reject an existing WASM output or derived proof-package path during job setup, while publication repeats the check before its atomic install.  An initial control package had regenerated the complete annotation sidecar, including the scalar loop, so that invalid comparison was interrupted before acceptance and replaced with an explicit length-dispatch selection that omitted only `function-0.while-loop-0`.

The corrected control completed Stage 5 in 2,262.084 seconds, including 2,161.901 seconds in Codex and 88.146 seconds in outer acceptance.  The candidate completed in 1,965.454 seconds, including 1,838.813 seconds in Codex and 114.900 seconds in outer acceptance, reducing total time by 296.630 seconds, or 13.113 percent.  Independent `leanexegen verify` accepted both packages over artifact digest `dbced77ae7a692ce49e98cb58721cb3c05a3712925e31685c4fd08dba4181be7` and proof-kit digest `f187032b357669bb82a3871d6490deefc7ba1e6b7d891cce883d2aed2d99b85f`.

The candidate proof uses the generated condition equation three times and body equation five times, with 12 `wp_run` applications and 635 lines.  The control uses 36 `wp_run` applications and 643 lines, and its journal records repeated discovery of checked-division guards, Boolean normalization, and emitted branch order.  The longer generated theorem names carry no penalty; the relevant structural change is the replacement of repeated symbolic-execution blocks with eight checked transition rewrites.

The compiler-side `ScalarCertificate` theorems justify scalar reification and descriptor emission, while the final artifact proof independently checks the descriptor against the exact decoded WAT region.  This indirect use is the first measured example of compiler theorems producing useful WAT-proof structure without entering the retained proof's trusted imports.  Both journals identify a checked function-entry-to-loop adapter as the next general increment because argument order, fixed-store quantification, and loop-head frame conversion still required repeated checks.

## 2026-08-08: Scalar-entry timing distribution

Three fixed-artifact runs with the checked entry-to-loop adapter completed Stage 5 in 1,282.711, 1,601.646, and 1,421.556 seconds.  Their 1,421.556-second median is 543.898 seconds, or 27.7 percent, below the 1,965.454-second matched compact-transition result, and their range is 318.935 seconds.  Median Codex time fell by 26.8 percent, while median independent outer acceptance fell by 41.7 percent.

The accepted proofs contain 548, 596, and 572 lines and use 9, 10, and 12 `wp_run` applications.  Every proof applies the generated entry equality once, `ScalarTransition.whileProgram_spec` once, and the compact condition and body equations, while their prime-factor lemmas and invariants differ.  The 572-line and 10-application medians reduce the matched proof by 9.9 and 16.7 percent, respectively.

All three journals report discovery of function zero's reversed WebAssembly operand stack before the lower-level entry equality applies.  The second journal also rebuilds word decrement through modular arithmetic, while the first and third use `UInt64.toNat_sub_of_le`; the second journal separately records an incompatible generic order instance for a `UInt64` comparison.  These repeated observations select an exact `TerminatesWith` adapter and fixed-width arithmetic guidance as the next general changes.

The generated `terminates_with_of_loop` theorem states the external operand stack in WebAssembly order and accepts a weakest-precondition proof beginning at the checked compact loop-head state.  Its first Lean check showed that `of_wp_entry_for` retained `func0Def.body`, and its second showed that unfolding left the function record's `toLocals` expression in an append-normal form; unfolding the definition and changing back to the generated frame closed both boundaries.  `tools/leanexegen annotate` then built the theorem for artifact digest `dbced77ae7a692ce49e98cb58721cb3c05a3712925e31685c4fd08dba4181be7`, and a separate `tools/leanexegen verify` accepted the successor package.

The third timing package passed its independent outer acceptance during publication.  A follow-up verification from the changing development tree rejected its older tool pins after the annotation generator and guidance had changed, before running Lean.  The successor annotation package binds the same accepted behavior proof to the new tool inputs and passed separate verification, preserving the distinction between an identity rejection and a proof rejection.

The arithmetic strategy now names `UInt64.toNat_sub_of_le` and `Project.ProofKit.Memory.toNat_sub_of_le`, and it directs unsigned inequalities through the `UInt64` `toNat` equivalences before applying natural-number order lemmas.  The proof-kit catalog now advertises fixed-width subtraction normalization in the memory module.  The next controlled run will expose the stronger entry theorem and revised guidance to a fresh proof session over the unchanged Demo 1 artifact before testing a semantically different scalar loop.

## 2026-08-08: Checked scalar-loop entry

The annotation consumer now recognizes a top-level scalar-loop entry when the decoded function has only `i64` parameters and locals and the preceding instructions contain supported constant and local transfers.  It evaluates that prefix symbolically and emits an artifact-specific theorem that equates the function-body weakest precondition with the named scalar-loop program, exact decoded suffix, and compact `U64State`.  The theorem remains generic over the module, host type, store, environment, postcondition, and scalar argument values.

The first Lean attempt executed the prefix but left `Locals.set?` normalization unresolved.  The second normalized the concrete local update and isolated the remaining mismatch between the decoded loop and the named descriptor program, after which a separate `rfl` tail equality avoided expanding the descriptor inside the entry proof.  Explicit reduction of `U64State.toState` and `State.toLocals` closed the final frame equality.

`tools/leanexegen annotate --only-region function-0.while-loop-0` built the resulting declaration for Demo 1's fixed 1,938-byte artifact, and independent `tools/leanexegen verify -s` accepted the package.  The checked recipe lists `function_0_while_loop_0_entry_to_loop` before the condition and body equations, while the proof instructions place its rewrite immediately after `TerminatesWith.of_wp_entry_for`.  A controlled fixed-artifact reproof will measure the complete Stage 5 effect and inspect the journal, accepted proof, and telemetry before the next change.

## 2026-08-08: Stronger scalar-entry screen

The controlled reproof applied the generated `function_0_while_loop_0_terminates_with_of_loop` theorem directly and completed Stage 5 in 1,418.100 seconds.  Codex took 1,326.745 seconds, outer acceptance took 79.367 seconds, and a separate `tools/leanexegen verify -s` run accepted the published package.  The result is 0.2 percent below the earlier entry-adapter median and remains inside that series' 318.935-second range.

The accepted proof contains 541 lines and five `wp_run` applications, compared with the earlier medians of 572 lines and ten applications.  It uses two checked condition equations and four checked body equations, while its journal records no reconstruction of the external operand-stack order.  The journal instead concentrates on the prime-factor invariant, arithmetic helpers, and `UInt64`-to-`Nat` conversions, and it uses the stronger adapter, singleton wrapper, scalar-loop theorem, and compact transitions supplied by the recipe.

This screen retains the stronger theorem because it removes repeated artifact-boundary work and reduces accepted proof structure.  The timing result does not justify another Demo 1 trial before testing semantic diversity.  The next loop will use a held-out scalar artifact and will consider general fixed-width arithmetic adapters only when the new journal confirms the same obstacle.

## 2026-08-08: Held-out Euclidean-loop baseline

Demo 6 maps a singleton `Array UInt64` to `gcd(x, 42)` through a separate imperative scalar helper and preserves arrays of every other length.  Its first generated source nested the loop inside the public wrapper, so that owned run stopped before artifact proof and the request was corrected to require the separate helper under test.  The accepted source and formal specification then passed on their first generated candidates.

The resulting 1,770-byte WASM module has SHA-256 digest `8126a2d03d514dd1335250b05fc9a1f9b89b84b55cc5b4d3e5a019c0ca6599cf`.  The compiler supplied the complete singleton-wrapper composition, length dispatch, and direct-call annotation, but supplied no loop annotation for function zero.  Stage 5 took 1,056.072 seconds, and a separate `tools/leanexegen verify -s` run accepted the final package.

The 191-line proof contains one `wp_loop_cons`, one `wp_run`, and seventeen `wp_iff_cons` applications.  Its journal records nine scalar edits spent on entry-store normalization, local-frame unfolding, fixed-index reduction, Boolean branch recovery, guarded remainder execution, the Euclidean invariant, and strict remainder decrease.  The wrapper theorem then accepted the scalar theorem and both formal-result equations without a further revision.

A managed `dump-ir` diagnostic found `Expr.loopFoldMultiSlot` beneath `Stmt.assign 12`, with initial accumulators `(input, 42)`, two body accumulators, a conditional remainder update, and result slot zero.  `annotationDocument` currently recognizes only top-level `Stmt.loopFoldMultiSlotAssign` and statement-level `Stmt.while`, which explains the missing region.  The next implementation will extend checked scalar-loop assistance to this expression form before running a fixed-artifact reproof.

## 2026-08-08: Checked scalar post-test loop

The compiler now recognizes `Expr.loopFoldMultiSlot` beneath a scalar assignment and emits `leanexe.loop.scalar-post-test.v1` when its staged body fits the typed scalar descriptor.  The region selects the exact top-level block and records the accumulator frame, initial values, result slot, destination, scratch boundary, body statement, and exit guard.  The descriptor language gained `UInt64` inequality because the emitter represents the done test with `i64.ne`, and the exact artifact equality must retain that instruction.

`Project.ProofKit.ScalarTransition.postTestProgram_spec` composes a body-first descriptor transition with an application invariant and decreasing measure.  `AnnotationMatches` also generates compact body and condition transition equations, an exact tail equality, a function-entry equivalence, and a `TerminatesWith` adapter.  The initial generated package failed exact equality when the descriptor represented inequality as equality followed by negation, after which the explicit inequality constructor made the decoded region equality reducible by `rfl`.

`tools/leanexegen annotate --only-region function-0.scalar-post-test-loop-0` recompiled Demo 6 to its preserved SHA-256 digest `8126a2d03d514dd1335250b05fc9a1f9b89b84b55cc5b4d3e5a019c0ca6599cf`.  The generated annotation module and a separate `tools/leanexegen verify -s` run accepted the new descriptor, transition equations, entry theorems, retained behavior proof, and final artifact theorem.  JavaScript tests now cover inequality validation, exact post-test branch shape, recipe selection, generated declarations, and rejection of a changed branch depth.

The first controlled reproof completed Stage 5 in 495.497 seconds, including 446.255 seconds in Codex and 35.786 seconds in outer acceptance.  The held-out baseline took 1,056.072 seconds, so the candidate reduces total time by 560.575 seconds or 53.1 percent.  A separate verification accepted the successor package over the unchanged formal specification, source, WASM bytes, and artifact digest.

The accepted proof contains 155 lines, compared with 191 in the baseline, and the journal records three edited candidates instead of nine.  It applies the generated `terminates_with_of_loop` theorem, `postTestProgram_spec`, `body_eval`, and `condition_eval`, retaining one `wp_run` while eliminating the baseline's raw `wp_loop_cons` and seventeen explicit `wp_iff_cons` applications.  Its remaining revisions cover the exact exit suffix and terminal compact-state normalization, and the journal reports no reconstruction of the checked remainder branch, staged accumulators, done flag, loop guard, or external operand order.

Two repeats of the retained configuration completed in 520.301 and 510.885 seconds.  The three accepted totals have a 510.885-second median and 24.804-second range, yielding a median reduction of 545.187 seconds or 51.6 percent from the held-out baseline.  Their proofs contain 155, 157, and 171 lines and require three, two, and two edited candidates, while every journal uses the checked scalar boundaries and concentrates on the Euclidean invariant and Lean presentation.

## 2026-08-08: Rejected scalar-exit adapter

The first post-test journal suggested a generated theorem for the exact result-copy suffix after the loop.  An experimental `exit_wp` theorem reduced the frozen three-instruction suffix from any compact scalar state and exposed the selected accumulator as the returned word.  Its generated proof, exact program match, recipe entry, annotation package, and independent verification all passed.

The controlled reproof used `exit_wp` in its zero-divisor branch and eliminated the candidate's remaining `wp_run`.  Stage 5 nevertheless increased from 495.497 to 633.288 seconds, including 580.715 seconds in Codex and 37.749 seconds in outer acceptance, while the accepted proof grew from 155 to 159 lines.  The journal records four edited candidates and new work determining explicit theorem arguments and retaining the folded compact state at the rewrite boundary.

The experiment remains 40.0 percent faster than the 1,056.072-second unannotated baseline, which confirms that the scalar post-test descriptor remains effective.  Both the primary time metric and secondary proof structure regress relative to the active candidate, so the exit theorem and its guidance were removed from the generator and recipe.  The independently verified experimental package remains under `benchmarks/leanexegen/demo6-gcd42/scalar-exit-candidate-2` for later analysis.

## 2026-08-08: Demo 6 compatibility and evidence

The repository-wide artifact conformance check accepted all 25 official execution files and all 15 official invalid modules.  Talos passed 3,853 cases, skipped 627 unsupported cases, and retained the six documented `memory_grow.wast` failures and the known imported-memory warning.  Wasmtime accepted every official file.

The aggregate artifact-proof check accepted all 20 artifact identities, embedded-byte comparisons, artifact theorem targets, behavioral specifications, axiom audits, and receipt results.  The public `demos/demo-6` package copies the exact accepted specification, source, WASM artifact, proof, annotations, generated annotation theorems, recipe, selected guidance, journal, telemetry, stage reports, and three-run timing record.  Its WAT rendering and direct samples expose the executable behavior without changing the proved artifact.

## 2026-08-08: Held-out counter-transfer loop

Demo 7 preserves every array except that a singleton passes through a scalar identity helper implemented by transferring a `UInt64` value from a decreasing counter to an increasing counter.  The generated 1,750-byte WASM artifact has SHA-256 digest `f437ebc16e352391ff05ff79d957eb7ef5652424d6d28c3f279e782980eeb7a5`.  Existing annotations matched the scalar post-test loop, length dispatch, direct call, and complete singleton wrapper without a compiler or annotation change.

The reference proof took 577.039 seconds, contained 171 lines, and required four edited candidates.  Its journal used the checked scalar and wrapper boundaries but derived an explicit value-pattern measure, modular decrement-and-increment preservation, nonzero decrement, and zero/one `toNat` normalization during the session.  Those repeated fixed-width obligations selected the next general LTG increment.

`ScalarTransitionU64` now defines `State.localU64ToNat`, `CounterTransition.decrement_add_increment`, and `CounterTransition.decrement_toNat_lt`.  Recipe construction traverses the checked scalar descriptor, reporting the counter theorems only for unit decrement and increment and reporting `U64Op.apply` for scalar binary operations.  Focused module and JavaScript tests accept the new declarations and descriptor-dependent recipe entries.

Three retained runs completed in 520.815, 405.284, and 816.771 seconds, giving a 520.815-second median and a 411.486-second range.  The median is 56.224 seconds, or 9.7 percent, below the reference, while median proof size fell from 171 to 135 lines.  The journals report three, one, and ten edited candidates, and all three accepted packages passed separate `leanexegen verify -s` checks under the final retained tree.

The slow retained run spent most of its revisions composing `postTestProgram_spec` with the generated scalar-entry theorem.  A checked generated `terminates_with_of_post_test` theorem removed that unification from the free-form proof, but three screens took 387.160, 558.581, and 748.263 seconds, giving a 558.581-second median and 140-line median proof.  Because this result is 7.3 percent slower than the retained configuration and does not reduce median edit count, the theorem and its recipe guidance were removed while the `composed-*` packages remain preserved.

The repository-wide conformance gate passed after the active configuration was restored.  Talos passed 3,853 official execution cases and retained the six documented upstream imported-memory failures as one warning, while Wasmtime passed all 25 official execution files and the validator accepted all 15 invalid modules.  The aggregate proof gate then accepted all 20 frozen artifact identities, embedded-byte comparisons, translation theorems, behavioral specifications, and axiom audits.

The next Demo 7 screen changed the deterministic singleton-wrapper starter to apply the complete wrapper theorem and expose three semantic cut points before Codex edited the proof.  Independent acceptance passed, but Stage 5 took 936.788 seconds, with 681.667 seconds in Codex and 203.555 seconds in outer acceptance.  This result is 79.9 percent above the retained median, so the active starter was restored and `cutpoint-rejected-1` preserves the failed experiment.

The rejected cut-point journal identified a mismatch between annotated combined-local indices and the local-list index accepted by `State.localU64ToNat`.  A candidate combined-coordinate helper removed that conversion, and all three agents used it directly at combined local three.  Their runs took 651.892, 577.172, and 521.718 seconds, producing a 577.172-second median, a 130.174-second range, and one edited-candidate median.

The coordinate screen reduced median edits from three to one but increased median Stage 5 time by 56.358 seconds, or 10.8 percent, and increased median proof size from 135 to 141 lines.  The helper and recipe entry were removed under the proof-time retention rule.  The three accepted packages and their journals remain in `combined-measure-1` through `combined-measure-3` so later work can reuse the coordinate observation without treating this screen as a timing improvement.

## 2026-08-08: Rejected focused proof context

Two Demo 7 journals found the selected wrapper and scalar proof structure without using irrelevant detailed catalog entries.  A deterministic selector omitted recipes inside the complete singleton-wrapper composition, retained the uncovered scalar-loop recipe, and reduced the combined prompt and supplied guidance from about 13,500 words to about 6,800 words.  The selected catalog contained detailed entries for `Array`, `ScalarTransition`, and `FixedArraySingletonWrapper`, while its compact fallback list preserved access to every permitted proof-kit module.

The fixed-artifact screens took 777.102 and 818.470 seconds, including Codex intervals of 618.059 and 648.934 seconds.  Their two-run median of 797.786 seconds is 277.971 seconds, or 53.2 percent, above the retained 520.815-second median.  A third run could not lower the candidate's three-run median below 777.102 seconds, so the experiment stopped after two accepted proofs.

Both journals applied the complete wrapper composition first, used the generated scalar entry and transition equations, and used both generic counter lemmas without a fallback import.  The accepted proofs contain 123 and 142 lines, compared with the retained 135-line median, but each agent still spent several full edit-and-build cycles constructing and normalizing the scalar invariant.  The selector therefore removed irrelevant reading without reducing proof-generation time, and the active generator restored the complete catalog and program-selected strategy context while preserving both packages under `focused-context-1` and `focused-context-2`.

## 2026-08-09: Checked counter-transfer summary

The focused-context journals locate the remaining Demo 7 work in the existential scalar-state view, invariant arithmetic, transition witnesses, and exit-state normalization.  A new generic `CounterTransition.postTestProgram_spec` theorem now proves sum preservation and strict measure decrease from a two-counter transition interface.  A hand-written application against the fixed Demo 7 artifact passed a focused Lean build, but it still had to name thirteen unrelated generated locals.

The annotation consumer now recognizes a semantic counter-transfer schema over a one-parameter, one-result scalar post-test function.  It checks the zero and nonzero body transitions, initial counter values, exit condition, store-neutral result suffix, returned accumulator, and exact generated entry state before emitting a complete store-preserving identity theorem.  The generated theorem applies the shared counter-transition theorem, while Lean checks its body equations, condition equations, loop entry, suffix execution, and conclusion against the decoded Program.

`tools/leanexegen annotate` generated and built the theorem for Demo 7's unchanged 1,750-byte artifact with digest `f437ebc16e352391ff05ff79d957eb7ef5652424d6d28c3f279e782980eeb7a5`.  A separate `tools/leanexegen verify -s` run accepted the resulting package.  JavaScript tests reject the semantic summary after changes to the initial result, counter update, exit condition, or returned accumulator; a controlled proof-generation timing screen remains pending.

Three fixed-artifact screens completed Stage 5 in 386.828, 371.243, and 354.004 seconds.  Their 371.243-second median is 149.572 seconds, or 28.7 percent, below the prior retained median, and their 32.824-second range is smaller than the prior 411.486-second range.  Separate `leanexegen verify -s` runs accepted all three preserved packages.

Every proof used the generated counter-transfer identity theorem as the scalar premise of `FixedArraySingletonWrapper.wrapperProgram_spec`.  The proofs contain 72, 68, and 67 lines, compared with the prior 135-line median, while the journals record one, one, and three edited candidates.  The remaining agent work concerns only the public singleton-array equations.

The out-of-sample compiler probe added an independent audit accumulator that increases by two.  Its scalar function has 23 locals, accumulator coordinates `[4, 5, 6]`, and result slot two, so the recognizer now searches the accumulator set for a unique remaining-and-result pair instead of assuming two fixed slots.  Unit tests retain this compiler-generated Program and sidecar and reject selection after changing the reported result slot.

A fresh Demo 8 run generated the specification, source, 1,793-byte artifact, checked annotations, and proof from prose.  The recipe selected the complete scalar theorem, and the first edited candidate used it in a 70-line proof that completed Stage 5 in 313.253 seconds.  A separate `leanexegen verify -s` run accepted the package under the new artifact digest `932262dad153458571234372e49c4142d7a7ea82cff4d09e2f2fd5eb276e4151`.

## 2026-08-09: Complete checked wrapper composition

The singleton-wrapper recipe now records the exact scalar callee from its checked direct-call annotation.  The deterministic proof starter applies `FixedArraySingletonWrapper.wrapperProgram_spec` when that callee has exactly one generated counter-transfer identity theorem, supplying the theorem before Codex begins.  Recipe validation checks the recorded callee against the wrapper call, retains compatibility with older stored recipes, and rejects a changed callee identity.

The production annotation command rebuilt the generated theorem against Demo 7's unchanged artifact, and the resulting package passed separate verification.  Three fixed-artifact reproofs then completed Stage 5 in 232.164, 201.366, and 204.537 seconds.  Their 204.537-second median is 166.706 seconds, or 44.9 percent, below the checked-summary median, and their 30.798-second range remains close to that configuration's 32.824-second range.

Each journal reports that the starter discharged the public wrapper and scalar loop before the first edit, leaving the invalid-length and singleton equations for `FormalSpec.expected`.  Every first edited candidate passed, and the proofs contain 73, 67, and 72 lines.  Separate `leanexegen verify -s` runs accepted all three packages over artifact digest `f437ebc16e352391ff05ff79d957eb7ef5652424d6d28c3f279e782980eeb7a5`.

LTG review now records role, scope, and evidence status separately.  Role is checked proof asset, annotation support, or worked example; scope is generic semantics, a compiler or runtime motif, or benchmark-local content; evidence status is promoted, provisional, or rejected.  Program names, fixed generated coordinates, application equations, and specification mathematics remain benchmark-local, while plausible narrow motif support may remain provisional as the small corpus accumulates independent consumers.

A benchmark-local accepted proof may remain as a non-importable worked example when it demonstrates a concrete proof organization, theorem application, diagnostic response, or annotation use.  Its catalog record must name the source artifact digest, intended lesson, illustrated declarations, feature tags, and derivative-exclusion group, and the proof journal must report any consultation.  The same artifact and close derivatives cannot receive the example during measured reproofs, and example use contributes no consumer evidence for its local lemmas.

The retention rule now treats worked examples as the default floor for checked LTG material that proves too specific for shared selection.  Generality and recurring-motif evidence determine importability, automatic selection, and promotion, while specificity alone does not justify discarding the example.  Invalidity, staleness, unsafe same-artifact disclosure, or duplication without a distinct lesson provide reasons for removal; sparse consultation evidence affects retrieval rank instead of preservation.

`CounterTransition.postTestProgram_spec` qualifies as generic, and the semantic recognizer has independent Demo 7 and Demo 8 consumers with different local layouts.  The identity-producing counter-transfer motif remains narrow and therefore retains motif status rather than standing for general loop support.  The complete composition mechanism is reusable for later checked callee summaries without incorporating either demo's formal identity equations.

## 2026-08-09: Demo 8 complete-composition trial

The unchanged complete-composition starter applied `FixedArraySingletonWrapper.wrapperProgram_spec` to Demo 8 and supplied `function_0_scalar_post_test_loop_0_terminates_with_counter_transfer_identity` for the wrapper's exact callee.  The proof journal reports that the initial build left only the invalid-length and singleton equations for `FormalSpec.expected`.  The first edited candidate proved those equations and passed the import check and full artifact build.

Stage 5 took 477.180 seconds, including 329.821 seconds in Codex and 93.210 seconds in outer acceptance.  The earlier Demo 8 run took 313.253 seconds, making this single trial 163.927 seconds, or 52.3 percent, slower.  Its accepted proof contains 72 lines and 265 words against the earlier proof's 70 lines and 235 words, and a separate `tools/leanexegen verify -s` run accepted the package over the unchanged artifact digest.

The result confirms that the checked starter transfers across the three-accumulator layout, but it does not show a proof-time gain on Demo 8.  The retained Demo 7 three-run distribution remains the timing basis for the starter.  `benchmarks/leanexegen/demo8-three-accumulator/complete-starter-1` preserves this negative timing result, accepted proof, journal, recipes, and telemetry.

## 2026-08-09: Residual specification normalization

The next starter variant discharged the two remaining wrapper premises by simplifying `FormalSpec.expected` in the invalid-length case and using `Array.size_eq_one_iff` before simplifying the valid case.  This deterministic step uses the residual theorem interface and the generated formal specification, without reading the accepted proof or application source.  JavaScript tests confirmed its selection after the checked wrapper and scalar summary.

Demo 8 accepted the untouched 67-line, 250-word proof in 219.561 seconds, including 114.709 seconds in Codex and 66.371 seconds in outer acceptance.  This run is 93.692 seconds, or 29.9 percent, below the initial 313.253-second Demo 8 proof.  A separate `tools/leanexegen verify -s` run accepted the package over the unchanged artifact digest.

Two fixed Demo 7 trials then accepted the same untouched 67-line, 250-word proof in 242.798 and 211.558 seconds.  Even an arbitrarily fast third trial would leave the three-run median at 211.558 seconds, 7.021 seconds, or 3.4 percent, above the retained 204.537-second median.  Both packages passed separate verification, but the active generator restored the prior starter under the proof-time rule.

The three accepted normalization packages remain worked examples.  They show how a deterministic proof can close definitional specification equations after checked artifact composition, and their journals document the zero-edit path.  Their timing status prevents automatic selection without erasing the technique or its evidence.

## 2026-08-09: Direct deterministic proof acceptance

The normalization journals show that Codex made no edit after receiving a complete starter.  Leanexegen now tries the complete checked counter-transfer starter in the outer proof workspace before starting the artifact-proof session.  An ordinary proof failure at the first artifact target starts Codex, while runner failures and failures in embedded-byte or declaration checks stop the run.

The first implementation performed a starter build and then repeated the full outer acceptance suite.  It used no Codex time but took 227.698 seconds, exceeding the retained 204.537-second median, so `double-check-rejected-1` preserves that accepted design failure.  The revised path uses one full check for both completeness and acceptance.

Three fixed Demo 7 runs of the consolidated path took 112.152, 125.103, and 156.268 seconds.  Their 125.103-second median is 79.435 seconds, or 38.8 percent, below the prior complete-starter median, and their range is 44.116 seconds.  Every run records zero Codex milliseconds, the same 67-line, 249-word proof, no edited candidate, and separate package verification.

Demo 8 then accepted the same mechanism over its three-accumulator layout in 212.727 seconds, including 185.912 seconds in the single outer acceptance and zero Codex time.  This is 100.526 seconds, or 32.1 percent, below its initial 313.253-second run.  Separate verification accepted the exact 1,793-byte artifact package.

The earlier residual-normalization packages remain worked examples because they record the proof technique and the cost of asking an agent to confirm an already complete proof.  The normalizer is now active only inside the checked counter-transfer wrapper starter, where the full Lean check determines whether it closes the generated specification.  A failed preflight does not discard the technique or conceal the diagnostic; it transfers the same starter to the normal artifact-proof session.

## 2026-08-09: Structured LTG retrieval

The LTG now stores canonical entries under `ltg/entries` and derives overlapping category indexes under `ltg/categories`.  Index records contain summaries, roles, scope, evidence status, features, annotation kinds, modules, declarations, and derived search terms, while full guidance remains in each selected entry's directory.  `tools/ltg check` validates metadata and generated indexes, and generated `Project.ProofKit.LTGCheck` asks Lean to resolve every advertised declaration.

Artifact-proof tasks receive the complete file tree after exact-artifact filtering, but the prompt supplies only a short retrieval protocol.  The agent starts at `LTG/categories.json`, searches JSONL indexes with `rg`, opens relevant entry bodies, follows supported related entries, and records its searches and decisions in the proof journal.  Exact artifact digests and caller-supplied derivative groups remove worked examples before any category index or entry body reaches the workspace.

The first fixed Demo 6 run found the scalar post-test, singleton-wrapper, and residual-normalization entries, rejected unrelated counter examples from index summaries, and revealed that declaration names were absent from searchable index fields.  It also searched unsuccessfully for Euclidean-GCD guidance after reaching the scalar arithmetic boundary.  Independent verification accepted its 141-line proof in 880.514 seconds, which was 72.4 percent above the retained median.

The revised index projection includes modules, declarations, and derived search aliases, while a provisional Euclidean-GCD entry records the invariant, divisor measure, and required `Nat.gcd` and remainder lemmas.  A second fixed-artifact agent found the wrapper, normalization, scalar-loop, and Euclidean entries through four category searches, opened only those entries, rejected unrelated counter, map, and filter material from summaries, and used all four selected entries.  Independent verification accepted its 153-line proof in 649.557 seconds, 26.2 percent below the first structured run and 27.1 percent above the retained median.

Structured LTG is now the canonical discovery mechanism for artifact-proof agents.  Schema-7 packages archive the exact filtered catalog view and a manifest containing the artifact filter, derivative groups, included and excluded entry IDs, and a digest over every archived LTG file.  Package validation checks the digest, category references, entry presence, and exclusion boundary, preserving retrieval provenance without making catalog prose part of the artifact theorem.

A synthetic scale test placed the real scalar-loop and Euclidean entries among 9,998 unrelated records in one category index.  The proof query returned only the two intended records and less than 10 KB of output, with observed local searches completing in tens of milliseconds.  This result tests file-level search selectivity and does not substitute for held-out proof-agent measurements on a large real catalog.

## 2026-08-09: LTG metrics

`tools/ltg metrics` now measures the validated catalog, generated indexes, and supplied proof-kit source under explicit counting rules documented in [LTG metrics](docs/ltg-metrics.md).  The initial snapshot contains 7 categories, 15 retrieval entries, 31 unique advertised declaration names, 22 distinct tactic commands, 39,642 canonical catalog bytes, and 430,185 bytes across the physical catalog and supplied proof kit.  Entries index 25 of 284 public named proof-kit declarations and have no structured tactic-name field, establishing declaration and tactic discoverability as measurable catalog-development work.

## 2026-08-09: Nested fixed-array fold annotation

Demo 9's wrapping-sum traversal lowers to an `arrayFoldMultiSlot` expression inside the sole value slot of `arrayLiteralSlots`, rather than to a top-level fold statement.  The new `leanexe.array.fold.v1` region tracks direct fold assignments and direct array-literal slot values through statement sequences, branches, and enclosing loops.  Its parameters record the widths, direction, bounds, accumulator and element roles, IR body, scratch layout, staged values, done state, release offsets, and result placement.

The consumer validates every field before resolving the structured path in the decoded Talos `Program`.  It checks the initialization locals, effective-stop boundary, forward or reverse guard, staged accumulator transfer, done branch, index update, back edge, and result-local copy, while `AnnotationMatches` fixes the complete selected interval by Lean equality.  JavaScript tests cover a nested forward fold, recipe selection, changed guard, and inconsistent scratch layout.

Recompiling Demo 9 preserved the 1,979-byte artifact and digest `aa263bbfa89c333f9fab497f1a2c370f476afc3419015d17b368cb7c8a6086d5`.  The emitted fold occupies instructions 39 through 65 of the valid branch at top-level instruction seven, and its recipe selects the three generic `ArrayFold.foldPrefix` declarations.  `tools/leanexegen verify -s` accepted the annotated package and its pre-existing exact-artifact proof under the current proof kit.

That verification also found a compatibility failure in an allocator tactic change: new default list simplifiers made an accepted proof's following `simp only` report no progress.  The established tactics retain their former simplification sets, while `wp_alloc_window_lists` and `wp_alloc_to_store_lists` provide the larger list-normalizing sets as explicit choices.  This preserves existing proof behavior and gives future journals a selectable response to concrete local-list reduction costs.

## 2026-08-09: Demo 9 fold-annotation reproof

The controlled fixed-artifact reproof used the same formal specification, source, 1,979-byte WASM module, and artifact digest as the baseline and earlier fold-prefix run.  Stage 5 completed in 3,188.251 seconds, including 3,119.979 seconds in Codex and 34.321 seconds in outer acceptance.  The result improves on the 3,431.870-second baseline by 243.619 seconds, or 7.1 percent, and on the 4,055.765-second fold-prefix run by 867.514 seconds, or 21.4 percent.

The accepted proof contains 416 lines, 1,848 whitespace-delimited words, and 17,797 bytes.  The baseline contains 493 lines, 1,844 words, and 16,312 bytes, while the prior fold-prefix proof contains 475 lines, 2,123 words, and 21,657 bytes.  Line count and repeated scaffolding decreased, while descriptive local names and shared declarations account for the current proof's word and byte distribution.

The journal records successful use of `wp_fixed_array_length_le_dispatch_from`, `wp_alloc_window_lists`, `wp_alloc_to_store_lists`, `FixedArrayAllocatorWindow.region_spec_withTail`, `ArrayFold.foldPrefix_succ`, `ArrayFold.foldPrefix_size`, and `UInt64Array.At.generatedElement`.  Two broad focused simplifiers exhausted one million heartbeats, after which named allocation, post-store, and loop-entry frames gave stable proof boundaries.  The agent retrieved the fold, length-dispatch, allocation, and memory entries, but its structured search did not find `generatedElement` because the array-memory entry had not advertised that declaration.

The array-memory entry now indexes `UInt64Array.At.generatedElement` and the `indexed-element-load` feature.  The fold recipe also names a generated exact program for the decoded interval and a Lean theorem proving that the structured path selects that program.  `tools/leanexegen verify -s` accepted the resulting package, and the LTG declaration check accepted the expanded catalog.

## 2026-08-09: Checked array traversal prefix

`Project.ProofKit.FixedArrayTraversalInput.dynamicProgram_spec` proves the standard dynamic `Array UInt64` element-address calculation and load for annotation-selected array, index, and item locals.  It derives the generated modulo address and memory read from `UInt64Array.At.generatedElement`, updates the item local, and accepts an arbitrary remaining program.  `continuingProgram_spec` adds the forward loop's unsigned effective-stop guard and false branch before applying the loader theorem.

The array-fold matcher now checks the exact one-word forward prefix before advertising either theorem.  For a match, `AnnotationMatches` names the nested 16-instruction interval as `continuingProgram` with the decoded local roles and proves the interval equality by reduction.  A changed or absent loader leaves the generic declarations out of the recipe, preventing an annotation from claiming a theorem whose program shape does not match.

Demo 9 retained its source, 1,979-byte WASM artifact, accepted behavioral proof, and artifact digest during this check.  `tools/leanexegen annotate` generated the nested equality at the loop path under valid-branch instruction seven and block instruction 62, and `tools/leanexegen verify -s` accepted the resulting package.  This result establishes theorem applicability and exact artifact linkage.  The following controlled reproof evaluates its use by a fresh proving agent.

## 2026-08-09: Demo 9 traversal-prefix screen

The controlled Demo 9 reproof found `fixed-array-traversal-input` through structured LTG and applied the generated continuing-program equality with `FixedArrayTraversalInput.continuingProgram_spec`.  That theorem discharged the complete sixteen-instruction guard, dynamic address, bounds, represented read, and item-local prefix.  The agent then completed the remaining accumulator update and loop measure proof without expanding the checked prefix.

The run produced no accepted proof after approximately 4,285 seconds, which exceeds the retained annotated run by about 1,097 seconds and the baseline by about 853 seconds.  The journal and candidate received no update for about twenty-two minutes after the agent began the completed branch and singleton representation, so the owned session was interrupted.  `benchmarks/leanexegen/demo9-fold-sum/traversal-prefix-censored-1` preserves the unfinished candidate, journal, exact annotation equality, recipes, selected guidance, and task inputs.

The journal identifies two reusable presentation rules.  Direct local-list getter facts should precede the focused traversal simplifier when the continuation depends on an explicit frame, and fixed-width addition equations must follow the proof kit's canonical simplifier orientation.  The artifact-proof prompt now asks the agent to record its intended change and expected residual before an extended construction or elaboration attempt, allowing a later stall to retain a precise proof boundary.

The completed-branch search also exposed a catalog omission.  `Project.ProofKit.FixedArrayResult` already contains continuation-generic length and payload-store theorems plus singleton and pair representation theorems, but no LTG entry advertised them.  The new `fixed-array-result` entry makes `payloadStore_spec` and `singletonStore_at` retrievable under the same `singleton`, `payload store`, `result suffix`, and `result construction` terms used by the stalled agent, and `LTGCheck.lean` resolves all four advertised declarations.

## 2026-08-09: Demo 9 result-store LTG run

The fresh Demo 9 agent found `fixed-array-result` on its first structured query and selected it for both output branches.  Its accepted proof applies `lengthStore_spec` twice, `payloadStore_spec` once, `singletonStore_at` once, and `FixedArrayTraversalInput.continuingProgram_spec` once.  Independent package verification accepted the 678-line proof over the unchanged 1,979-byte artifact and SHA-256 digest.

Stage 5 took 3,149.420 seconds, including 3,076.065 seconds in Codex and 46.637 seconds in outer acceptance.  The journal records two broad dependency-repository searches whose path-only results included external demo and benchmark proofs, although the agent reports opening only selected proof-kit files and using no external proof.  Those searches violate the measurement boundary, so the package remains capability evidence and its time is censored.

The run repeated the inference failure caused by the direct length-dispatch tactic before using `_from hArray`, then spent its later iterations on fold setup and the seven-update successor frame.  Generated length recipes now advertise their `_from` variants, and `FixedArrayResult.emptyStore_at` closes the zero-length output representation from its two bounds.  The next fold increment should provide checked setup and successor-frame boundaries rather than another broad simplifier configuration.

The two prohibited searches identify a task-isolation problem.  Each artifact-proof workspace now contains `PROOF_KIT_SOURCE/`, a source mirror of every allowed proof-kit module, and the prompt directs all proof-kit searches to that tree.  This keeps declaration inspection inside the isolated task while preserving the existing proof-kit source digest and import allowlist.
