# Development Plan

## Goal

LeanExe should compile useful first-order Lean programs into small WebAssembly artifacts whose behavior can be checked against the source and proved for the code that ships.  The current application target is the central-limit-order-book kernel in `LeanExe/Examples/Clob.lean`, because it exercises scalar logic, arrays of structures, search, allocation, copying, ownership, and multi-result ABIs in one coherent program.  New language support should follow a concrete need from this target or another program selected in discussion.

Correctness has three layers.  Differential tests compare standard Lean, the IR interpreter where it applies, and Wasmtime; artifact checks compare regenerated WASM and WAT byte-for-byte with the proof inputs; Talos proves quantified properties of the decoded shipped instructions.  Documentation must state which layer supports each claim and must retain the trusted-base boundary described in [Verifying a Program](verifying.md).

## Current Baseline

| Area | Established state | Open issue |
|------|-------------------|------------|
| Accepted language | First-order pure programs over scalars, byte arrays, fixed-width arrays, structures, tagged values, internal recursive values, supported loops, and selected specialized helpers. | Source-level `LeanExe.Runtime.release` has an ownership precondition that the compiler documents but does not check. |
| Compiler | Checked-environment extraction, a typed first-order IR with an interpreter, ownership summaries, a reference-counted heap, and one structured WASM instruction stream serialized as binary or WAT. | Flattening some matched multi-slot values repeats their computation.  `cancel` scans for the same identifier three times. |
| Execution tests | `node test/run_all.js` passes 784 accepted cases, 34 rejections, 13 traps, 301 standard-Lean comparisons, 58 IR comparisons, and the ABI, WASI, allocation, ownership, and fuzz suites. | The full run is verbose and expensive.  Several heap-valued cases lack an IR-interpreter comparison. |
| Artifact proofs | Fourteen byte-pinned Talos cases pass, including the self-compiled LEB128 encoder, CLOB quote, and the not-found branch of CLOB cancel. | The found branch of `cancel`, followed by `postOnly`, `limit`, and `market`, remains unproved. |
| Documentation and tools | The repository has a specification, manual, verification guide, proof README, and chronological development journal.  Lean, Wasmtime, and Talos revisions are pinned. | The root README, proof README, summary, and agenda predate the last three artifacts.  The CLI help text is stale, `wasm-tools` is unpinned, and Lean reports unused proof arguments. |

The baseline above was checked on 2026-07-13.  The untracked `leanclob/` directory is a separate nested Git repository and is outside this plan.  A future review should update this table when a phase below changes a stated fact.

## Development Rules

Keep one representation and one implementation for each semantic operation.  The structured instruction list in `LeanExe/Wasm/Instr.lean` remains the sole lowering result for both binary and WAT serialization, and compiler changes must explain every affected artifact from the IR or instruction diff.  Add an abstraction after repeated proof or compiler code establishes its common shape.

Accepted programs must fail closed.  An unsupported source form must stop compilation with a message that identifies the entry, the relevant declaration or expression, and the violated restriction.  Memory ownership, evaluation order, ABI layout, traps, and integer bounds are semantic behavior and require focused tests whenever they change.

Keep changes narrow.  A compiler change should include its smallest source fixture, IR or ownership assertion, execution comparison, rejection case when applicable, documentation edit, and affected artifact update.  Dependencies and trusted-base changes require discussion before implementation.

## Work Order

### 1. Check Explicit Release Ownership

`LeanExe.Runtime.release` changes generated memory while its ordinary Lean definition is a zero-returning stub.  The specification requires the released root and every shared node reachable from it to be absent from later live values, but the compiler currently accepts that condition as a caller assertion.  The next compiler change should accept an explicit release only when existing owner provenance, alias propagation, and liveness analysis establish the required handoff.

The implementation should begin after maintainers settle one design choice.  The preferred design restricts the current intrinsic to roots whose uniqueness the compiler can establish, including existing examples that transfer a fresh root at its last use.  If the analysis cannot establish an example's handoff, move that use to a test-only intrinsic or redesign the example instead of weakening the check.

- [ ] State the accepted ownership condition for owned roots, borrowed owner-zero arrays, container children, and repeated release.
- [ ] Reject a release followed by a use of the root or an unretained alias, including aliases passed through a local, structure, tag, array, helper result, or return value.
- [ ] Preserve the existing positive release cases whose ownership the analysis establishes.
- [ ] Add exact rejection tests for use after release, double release, and release through a live alias.
- [ ] Include the source declaration and release reason in the diagnostic.
- [ ] Update the specification, manual, README, ownership report, and development journal in the same change.

This phase ends when every accepted source-level release has a compiler-checked ownership justification.  The ordinary execution suite must pass, and the ownership report must expose enough provenance to explain each accepted or rejected handoff.  Artifact bytes should remain unchanged for programs that do not call the intrinsic.

### 2. Evaluate Matched Values Once

The CLOB `cancel` artifact evaluates one `Array.findIdx?` match result three times while flattening the returned structure.  The source evaluates the scrutinee once, and the repeated scans enlarge the artifact and multiply proof obligations.  Fix the extraction boundary that duplicates the value by materializing the matched result into locals once and reusing those locals for projections and branch results.

The change should target repeated value extraction rather than introduce a general common-subexpression pass.  Local materialization must preserve lazy field demand, trap order, branch selection, and owner provenance.  Existing demand and ownership analyses should consume the same local representation so evaluation and release rules remain aligned.

- [ ] Add a reduced fixture that reproduces one repeated `findIdx?` result across a multi-slot return.
- [ ] Assert in the IR test that the search appears once.
- [ ] Compare standard Lean, IR evaluation where supported, and generated WASM on found and missing inputs.
- [ ] Confirm from `dump-ir` and WAT that `cancel` contains one identifier scan.
- [ ] Check byte changes for every affected Talos artifact before updating any proof input.

This phase ends when `cancel` performs one scan and the full execution suite passes.  The compiler change must include a concise explanation of why any other artifact changed.  The transactional Talos update path remains the only way to replace affected proof inputs.

### 3. Prove Complete Cancel Behavior

Regenerate the CLOB cancel artifact after the single-evaluation fix, then prove both result branches.  The theorem should quantify over every well-laid-out order array and identifier, return the same status and book as the Lean `cancel` function, and state the memory and ownership frame for borrowed and newly allocated results.  The existing `OrdersAt`, `idIdx`, and scan lemmas should remain the source-level bridge.

- [ ] Repair the not-found proof against the updated artifact without weakening its statement.
- [ ] Add the index-recording scan lemma needed by the found branch.
- [ ] Prove the inline allocation, header initialization, and both element-copy loops for `eraseIdx!`.
- [ ] State the returned array owner, length, contents, counters, and unchanged-memory region.
- [ ] Run `tools/check-talos-clob-cancel.sh`, `tools/check-talos.sh`, and `node test/run_all.js`.

This phase ends with one `cancel_correct` theorem covering found and missing identifiers.  The proof may use the standard axioms already present in the workspace and must contain no `sorry`, new axiom, or unchecked artifact replacement.  The proof README and verification table must describe the complete theorem rather than the former branch-only result.

### 4. Prove the Remaining CLOB Kernel

Proceed in dependency order so each theorem supplies facts used by the next.  `postOnly` comes first because it adds validation, crossing checks, and one appended order without the matching loop.  `limit` and `market` follow after generic theorems for `findBest` and `matchFuel` establish price priority, FIFO behavior at equal prices, same-trader exclusion, quantity conservation, and termination under the explicit fuel bound.

| Step | Required theorem coverage |
|------|---------------------------|
| `postOnly` | Invalid order, duplicate identifier, would-cross result, successful append, borrowed results, allocated results, and empty trade array. |
| `findBest` | The returned index identifies the best eligible maker, with the first array index breaking equal-price ties. |
| `matchFuel` | Each iteration removes or reduces one maker, preserves unrelated orders, records one trade, conserves quantity, and consumes fuel. |
| `limit` | Invalid, fully filled, partially filled, and unfilled orders, including returned book and trade-array contents. |
| `market` | The same matching result under the price-unlimited taker transformation, with no residual taker insertion. |
| `depth` | Per-side aggregation after the matching operations, reusing fixed-width array and fold lemmas. |

Each artifact theorem must quantify over meaningful input rather than prove a fixed scenario checksum.  Differential fixtures should cover every source branch before proof work begins.  A compiler gap discovered here becomes a separate reduced compiler task with its own acceptance tests.

### 5. Consolidate Proof Machinery from Repetition

The CLOB proofs will repeat fixed-width array reads, copy loops, allocation headers, and ownership frames.  Move a pattern into `Project/Common.lean` or the runtime library after two independent cases use the same statement shape and a third case would repeat it.  Keep generated `Program.lean` files untouched and keep artifact-specific address arithmetic near the artifact when no stable general statement exists.

- [ ] Generalize the fixed-width array predicate used by quote and cancel when the next CLOB proof confirms its shape.
- [ ] Generalize copy-loop and fresh-array postconditions used by `eraseIdx!`, `push`, and later matching updates.
- [ ] Extend `release_frees_tree` to array-kind nodes, then to shared interior nodes and aliased shared leaves.
- [ ] Reprove `pair_free` and `box_free` as applications of the general teardown library and remove their duplicated walk proofs.
- [ ] Add normalizing lemmas or tactics only for address and invariant forms that recur across artifact modules.

This phase ends when allocation-bearing CLOB proofs depend on shared semantic lemmas instead of copied instruction walks.  Reduced proof size is evidence, while theorem statements and build time provide the acceptance checks.  A refactor must preserve every artifact theorem and the complete proof build.

### 6. Prove a Stable Lowering Fragment

After the CLOB helper boundaries stabilize, prove lowering correctness for the scalar fragment shared by `gcd`, `order_book`, CLOB scans, and CLOB decision logic.  The fragment should cover locals, calls, 64-bit operations, conditionals, lets, structured loops, and traps, relating IR evaluation to the Talos execution model.  Existing artifact theorems remain the shipping guarantee while this theorem reduces repeated instruction proofs.

The representation choice requires discussion before implementation.  A direct translation from the compiler's structured `Wasm.Instr` and module values to Talos values permits a universally quantified theorem, while byte-pinned artifact checks continue to connect generated binaries to decoded shipped code.  The proposal must state the additional trusted code, the agreement check with Talos decoding, and the exact fragment before adding the dependency boundary.

## Diagnostics and Documentation

Diagnostics are part of every phase.  Before changing exit behavior, define and document a small CLI error scheme that separates invalid arguments, unsupported source, I/O failure, and internal inconsistency.  End-to-end tests should assert exit status and stderr for a missing module, missing entry, wrong entry type, unsupported declaration, invalid bound, reserved export name, and failed output write.

Error text should provide enough context to fix the source.  Include the command, module, entry, declaration, and rejected construct where those values exist, while preserving the most specific extractor reason.  Keep stdout for requested reports and artifacts, stderr for failures, and omit color and progress decoration from repository-owned output.

The documentation files now have distinct responsibilities.  The README gives setup and a short overview; `DEVELOPING.md` defines developer setup, diagnostics, gates, generated files, and troubleshooting; the manual explains source authoring; the specification defines accepted semantics and rejection boundaries; the proof README lists current artifact theorems; the verification guide explains the proof process; this file orders future work; and `devnotes.md` records history and rationale.  `agenda.md` is an archived pointer, while `summary.md` explains architecture without maintaining a second roadmap.

CLI help now includes `dump-ir` and `compile-wat`, the obsolete prototype description is gone, and the proof inventory contains all fourteen cases.  The setup documentation explains both pinned Lean versions and records the unpinned Node and `wasm-tools` versions as reproducibility gaps.  Warning cleanup remains separate: remove the `AsciiDigits.lean` warning directly, then remove proof warnings when semantic work already requires editing the affected file or when maintainers approve a focused cleanup.

## Reproducible Gates

Pin every tool that can change generated or decoded artifacts.  Talos already uses a commit revision and Wasmtime uses a release version; add a checked `wasm-tools` version, verify downloaded Wasmtime archives, and record the required Node version.  Keep dependency setup separate from the gate summary so a cold Mathlib build cannot obscure an artifact mismatch or theorem failure.

| Change | Required checks |
|--------|-----------------|
| Documentation only | `git diff --check`, local-link review, and command review for every changed example. |
| Source example | Targeted Lake build, source guards, standard-Lean comparison, and the relevant execution test. |
| Extraction, IR, ownership, ABI, or WASM emission | Targeted fixture, `node test/run_all.js`, `tools/check-wat.sh`, every affected artifact script, and `tools/check-talos.sh`. |
| Artifact proof | The per-case script, `lake build Project` in the proof workspace, and the execution test for the source entry. |
| Toolchain update | Full execution and proof gates, artifact byte review, documented version and checksum, and trusted-base review. |

The standard comparison runner should gain a quiet summary mode and timing by entry.  Reuse one compiled artifact for repeated inputs only after a trace proves that the cache key includes the module, entry, adapter mode, compiler binary, and all ABI bounds.  This maintenance follows the semantic work above unless test duration blocks development.

## Completion Criteria

This plan reaches its next stable point when explicit releases are compiler-checked, matched values evaluate once, and the CLOB `cancel`, `postOnly`, `limit`, and `market` artifacts have input-generic Talos theorems tied to their shipped bytes.  The execution suite, WAT round trip, ownership checks, and all artifact proofs must pass under pinned tools.  User-facing commands must report failures with enough source context, and the specification, manual, proof table, and journal must agree with the implementation.
