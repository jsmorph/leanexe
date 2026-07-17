# Development Plan

## Goal

LeanExe should compile useful first-order Lean programs into small WebAssembly artifacts whose behavior can be checked against the source and proved for the code that ships.  The current application target is the central-limit-order-book kernel in `LeanExe/Examples/Clob.lean`, because it exercises scalar logic, arrays of structures, search, allocation, copying, ownership, and multi-result ABIs in one program.  New language support should follow a concrete need from this target or another program selected in discussion.

Correctness has three layers.  Differential tests compare standard Lean, the IR interpreter where it applies, and Wasmtime; artifact checks compare regenerated WASM and WAT byte-for-byte with proof inputs; Talos proves quantified properties of decoded shipped instructions.  Each claim must identify its layer and retain the trusted-base boundary described in [Verifying a Program](verifying.md).

LeanExe runtime intrinsics require a separate semantic statement.  Ordinary Lean evaluates `LeanExe.Runtime.release` and the runtime counters as stubs, while generated WASM gives them memory-management behavior.  Programs that use those intrinsics cannot claim ordinary Lean equivalence for the intrinsic observations; they require the extended runtime semantics defined in Phase 1 and artifact-level evidence for the emitted implementation.

## Current Baseline

| Area | Established state | Open issue |
|------|-------------------|------------|
| Accepted language | First-order pure programs over scalars, byte arrays, fixed-width arrays, structures, tagged values, internal recursive values, supported loops, and selected specialized helpers.  Runtime intrinsics have separate ordinary-Lean and generated-WASM semantics, and every accepted explicit release has a compiler-produced direct-handoff judgment. | Branch-dependent roots, conditionally owned arrays, consuming parameters, structure fields, and loop-carried release roots remain deferred until a focused ownership analysis proves them. |
| Compiler | Checked-environment extraction, a typed first-order IR with an interpreter, ownership summaries, a reference-counted heap, and one structured WASM instruction stream serialized as binary or WAT.  Array search matches bind one encoded scan result before projecting the tag and payload.  Exported natural-number recursion initializes its internal carried state from the public ABI, materializes aggregate state once, and tracks only loop-created owners. | The remaining CLOB exports require input-generic proofs in dependency order, beginning with `limit`. |
| Execution tests | The complete gate passes 791 accepted cases, 45 rejections, 14 traps, 340 standard-Lean comparisons, 62 IR comparisons, 41 reference-counting cases, 9 CLI failure cases, 3 process-launch error cases, and the matched-value IR and WAT assertions. | The IR interpreter does not model heap allocation, release, or runtime counters. |
| Artifact proofs | Seventeen completed byte-pinned proof cases exist, including the self-compiled LEB128 encoder and exact CLOB quote, cancel, `findBest`, `postOnly`, and `matchFuel` behavior.  The source matcher has exact step and natural-number quantity-conservation theorems. | `limit`, `market`, and `depth` remain unproved. |
| Documentation and tools | The current documents identify all seventeen checked proof cases as complete.  The compiler and proof workspaces pin Lean 4.31.0, Node pins 24.13.0, `wasm-tools` pins 1.251.0, Wasmtime 44.0.0 archives have checked hashes, repository instructions constrain every Lean process, CLI failures use tested statuses and contextual stderr records, and Talos artifact comparisons run before a separate proof-freshness check. | Older handwritten proof files retain linter warnings.  Warning-only builds of `SharedPair` and `LebU32.Iter` exceeded 30-minute and 15-minute limits under memory pressure, so those warnings remain until substantive work requires the same elaboration. |

The baseline was checked on 2026-07-15.  The untracked `leanclob/` directory is a separate nested Git repository and remains outside this plan.  Update this table in the same change that alters a stated fact.

## Development Rules

Keep one representation and one implementation for each semantic operation.  The structured instruction list in `LeanExe/Wasm/Instr.lean` remains the sole lowering result for binary and WAT serialization, and a compiler change must explain each affected artifact from the IR or instruction diff.  Add an abstraction only after repeated compiler or proof code establishes a common statement.

Accepted programs must fail closed.  An unsupported source form must stop compilation with a message that identifies the command, entry, relevant declaration or expression, and violated restriction.  Memory ownership, evaluation order, ABI layout, traps, and integer bounds are semantic behavior and require focused tests whenever they change.

Keep changes narrow.  A compiler change should include its smallest source fixture, an IR or ownership assertion, an execution comparison, a rejection case when applicable, a documentation edit, and review of affected artifact bytes.  Discuss dependencies, trusted-base changes, and representation choices before implementation.

## Work Order

### 1. Define Runtime Intrinsic Semantics and Check Direct Handoffs

`LeanExe.Runtime.release` consumes one owned root reference in generated code and returns `freeCount` after the release.  Root ownership does not require graph-wide uniqueness: a child shared with another live value remains valid when allocation or copying retained the other reference correctly.  The unsafe case is another live alias to the same owned root, or another unretained reference whose lifetime depends on the consumed root.

The specification must distinguish ordinary Lean semantics from LeanExe's runtime extension.  Standard-Lean differential claims exclude runtime-intrinsic observations, while the extended semantics defines counter reads, release of an owned root, release of a statically borrowed owner-zero array, recursive child decrements, and the returned counter value.  The Talos runtime theorems remain the evidence for the emitted release implementation until a general source-to-runtime theorem exists.

The first checker should accept a bounded set of handoffs: a direct local root from a visible fresh allocation or a helper result marked fresh, consumed at its final use, with no copy, return, container escape, or second release of that root reference.  It may accept an array whose owner is statically known to be zero because the generated release is a no-op.  A value whose ownership depends on a branch, structure field, loop-carried state, or unresolved alias must reject until a later increment proves that shape.

Existing explicit-release examples need an audit against this rule.  A user-facing example that the initial checker cannot justify may be rewritten to expose a real handoff, or its required ownership analysis may become a separate reduced compiler task.  Do not add a test-only or unchecked intrinsic that bypasses the accepted-language check.

- [x] Define the extended semantics for runtime counters and `Runtime.release`, including its relationship to ordinary Lean evaluation and the IR interpreter's current limits.
- [x] Define the static judgment for one owned root reference, final use, transfer, retained sharing, owner-zero arrays, and repeated release.
- [x] Inventory every explicit release and classify the provenance and later uses of its root.
- [x] Accept direct fresh-local and fresh-helper-result handoffs that satisfy the initial judgment.
- [x] Accept statically known owner-zero array releases as no-ops, and reject ownership that is only conditionally zero.
- [x] Reject use after release, double release, direct unretained aliases, container escape, return escape, and unsupported interprocedural aliases.
- [x] Include the source declaration, released expression, provenance, and rejection reason in diagnostics and the ownership report.
- [x] Add exact rejection tests and Wasmtime counter tests; use Talos runtime theorems for the emitted recursive-release behavior.
- [x] Update the specification, manual, repository overview, developer guide, and journal in the same change.

This phase completed on 2026-07-13.  Every accepted explicit release has a compiler-produced ownership justification, and unsupported shapes reject with source context.  The complete execution suite, ownership-report tests, nine-entry WAT round trip, and all fourteen artifact checks pass; programs without runtime intrinsics retain their ordinary Lean comparison claim, while intrinsic-using programs state the extended semantic boundary.

### 2. Evaluate Matched Values Once

The prior CLOB `cancel` artifact evaluated one `Array.findIdx?` match result three times while flattening the returned structure.  Lean evaluates the scrutinee once, and the repeated scans enlarged the artifact and multiplied proof obligations.  The extractor now binds an encoded scan result once and reuses its normalized tag and payload through a statement-level branch.

The change should target repeated value extraction rather than add a general common-subexpression pass.  Local materialization must preserve branch selection, demand, trap order, and owner provenance.  Demand and ownership analyses must consume the same local representation so evaluation and release decisions remain aligned.

- [x] Add a reduced scalar fixture that repeats one multi-slot match result and assert that its IR contains one scrutinee evaluation.
- [x] Add a branch fixture whose unused payload traps if evaluated, proving that materialization does not make payload fields strict.
- [x] Add a heap-bearing match result that checks owner transfer, returned roots, and absence of duplicate allocation or release.
- [x] Compare standard Lean, IR evaluation where supported, and generated WASM for found, missing, and trapping inputs.
- [x] Confirm through `dump-ir` and WAT that CLOB `cancel` contains one identifier scan.
- [x] Review every changed Talos artifact before updating a proof input.

This phase completed on 2026-07-13.  The full execution suite and aggregate Talos gate pass, including the WAT assertions and every affected byte-pinned artifact.  The reviewed cancel diff removes two scan loops, adds one encoded-index local, and retains the found-branch allocation and copy loops with renumbered locals; the related statement-level branch change also reduced the quote artifact after its proof was updated.

### 3. Prove Complete Cancel Behavior

Regenerate the CLOB cancel artifact after the single-evaluation fix, then prove both result branches.  The primary theorem should quantify over every well-laid-out order array and identifier and relate the result exactly to the Lean `cancel` function under `UInt64` semantics.  Its postcondition must distinguish the borrowed not-found book from the fresh found-branch array and state counters, contents, and unchanged memory.

- [x] Repair the not-found proof against the updated artifact without weakening its statement.
- [x] Add the index-recording scan lemma needed by the found branch.
- [x] Prove the inline allocation, header initialization, and both element-copy loops for `eraseIdx!`.
- [x] State the returned owner, array length, elements, runtime counters, and unchanged-memory region for each branch.
- [x] Run `tools/check-talos-clob-cancel.sh`, `tools/check-talos.sh`, and `node test/run_all.js`.

This phase completed on 2026-07-13 with one `cancel_correct` theorem covering found and missing identifiers.  The proof uses only the standard axioms already present in the workspace and contains no `sorry`, new axiom, or unchecked artifact replacement.  The proof README names the complete theorem, and the focused cancel check, aggregate proof build, and complete execution suite pass.

### 4. Prove the Remaining CLOB Kernel

State the source-level properties before proving instruction streams.  Each primary artifact theorem should relate the export exactly to its Lean function for every well-laid-out input under `UInt64` semantics.  Additional economic properties should use natural-number quantities with explicit no-overflow bounds, or state modular conservation when no such bounds are assumed.

Define the shared preconditions once.  They must cover memory layout and page bounds, array lengths and indexes, valid sides where an economic property requires them, identifier uniqueness where required, nonzero quantities where required, and the fuel relation to book length.  Every allocation-bearing result must state whether each returned array is borrowed or owned, its root and contents, counter changes, and the memory region preserved from the input.

Proceed in dependency order so each theorem supplies facts used by the next.  Prove `findBest` before `postOnly`, because the export calls that search directly.  Prove `matchFuel` before `limit` and `market`, while `depth` can follow once the common array and ownership lemmas are stable.

| Step | Required theorem coverage |
|------|---------------------------|
| `findBest` | Exact source result for every input; under valid-side assumptions, best eligible price with the first array index breaking equal-price ties. |
| `postOnly` | Invalid order, duplicate identifier, would-cross result, successful append, borrowed results, fresh results, and empty trade array. |
| `matchFuel` | Exact source result plus termination; every step removes or reduces one maker, preserves unrelated orders, records one trade, and conserves maker and taker quantities over natural-number totals. |
| `limit` | Invalid, fully filled, partially filled, and unfilled orders, including exact book and trade-array contents and ownership. |
| `market` | Exact matching behavior under the price-unlimited taker transformation, with no residual taker insertion. |
| `depth` | Exact per-side aggregation, order of first price occurrence, bounded or modular quantity totals, and ownership of both result arrays. |

Differential fixtures must cover every source branch before proof work begins.  A compiler gap discovered here becomes a reduced compiler task with its own fixture and acceptance tests.  An artifact theorem must quantify over meaningful input rather than certify a fixed scenario checksum.

The `findBest` step completed on 2026-07-14.  Its artifact theorem returns the exact source `Option Nat` for every represented order array, every taker, and every input length below `2^32`, while preserving the store.  Its source theorem proves that a returned maker is eligible, no eligible maker has a better price, and the first array index breaks equal-price ties.  The focused branch gate covers empty input, rejected makers, an eligible maker after a rejected prefix, both taker sides, better candidates, worse candidates, and equal-price FIFO ties.  The public-ABI matrix now covers every planned kernel entry without a source wrapper: seven `postOnly`, five `matchFuel`, six `limit`, five `market`, and two `depth` cases.  The matrix also includes a reduced recursive aggregate-state case that detects owner-and-pointer corruption across more than one iteration.

The expanded matrix exposed a compiler error before further proof work began.  Exported recursion had assigned the compact public ABI slots positionally to a larger internal state containing owner-and-pointer pairs, which corrupted nested CLOB state after the first iteration.  The compiler now initializes separate internal carried locals, evaluates fresh aggregate arguments once, and releases only loop-created owners that the next state no longer retains.

The `postOnly` step completed on 2026-07-15 with three input-generic theorems covering invalid, crossing, and successful append results.  The theorems state exact public values, borrowed or fresh book ownership, empty trade-array allocation, allocator globals and counters, and preservation below the prior heap top.  `Project.ClobPostOnly.Spec` passes `--wfail`, so `matchFuel` is the next CLOB export in dependency order.

The `matchFuel` proof now has a list-level source model, a source-defined full-fill count for release counters, shared trade-array representation, verified embedded `findBest`, and exact theorems for the zero-fuel, zero-remaining, and no-maker exits.  Its generated runtime suite matches the shared allocator, reset, retain, and release definitions.  Module-generic theorems prove fixed-array release and first-fit free-list deletion, while artifact theorems prove every generated book and trade allocator layout, both fit and bump outcomes, both erased-book copy loops, the post-allocation partial-fill copy and quantity replacement, and the common trade copy and append stores.  Allocator frame theorems preserve a disjoint live source array, including its release header, through either allocation outcome and supply the payload separation used by the copy loops.  All three allocation, copy, and final-store paths now compose for both outcomes while retaining the selected free-list choice or bump predecessor, target bounds, source ownership, and outside-payload frames.  The generated release guard block has a generic theorem for two owned arrays and exact no-call and trade-only theorems for the tracker states reached by the full-fill loop; each semantic release theorem preserves both replacement arrays and updates the represented free list.  The complete full-fill step composes all four allocator outcomes with the reachable tracker release and recursive transition cases, preserving replacement bounds, bounded heap growth, free-list separation, free-node bounds, page count, allocator scratch local types, and the exact recursive frame for the next iteration.  The partial-fill branch preserves both result arrays, allocator state, and unchanged release counters.  The iteration dispatcher composes the remaining-quantity test, embedded search, maker-quantity read, completion exits, and exact full-versus-partial branch continuations while preserving the loop-carried book owner.  A separately compiled loop invariant states recursive source progress, ownership, allocator state, exact counters, page bounds, heap budget, and byte equality above the reserved heap boundary for running states, and exact public output facts for completed states.  Shared step bounds derive both allocation branches' length, byte, no-wrap, page-fit, and reserved-boundary premises from that invariant.  Source-progress, completion, and full-advance constructors establish invariant preservation for every dispatcher outcome, branch-composition theorems connect both allocation-bearing continuations to those constructors, and the dispatcher composition returns the invariant with a strictly smaller loop measure through all nested branch continuations.  The generated guard-dispatch loop terminates with either a completed result or a zero-fuel running state, and the initial-state constructor establishes the complete running invariant from public memory and allocator premises.  One result predicate covers both exit forms, and the generated epilogue returns the exact source remaining quantity, represented book and trade arrays, free list, allocator counters, page count, and reserved-boundary memory frame.  The full- and partial-fill program definitions retain the generated nested one-result branches instead of flattening their allocator continuations.  `Entry.func14_decomposition` proves that the generated function body equals initialization followed by the verified loop and result epilogue, and `Entry.initialized_loop_locals` connects the public ABI frame to the initial loop data.  `ClobMatchFuel.Correct.matchFuel_correct` proves termination and the exact source `matchFuelL` result for every represented input under the stated allocator and budget premises.  `ClobMatchFuel.Properties.matchFuelL_steps` supplies exact full- and partial-step decomposition, while the associated preservation lemmas and `matchFuelL_quantity_conservation` establish natural-number maker and taker conservation without an overflow premise.  The next artifact theorem is `limit`.

The `clob_limit` case is registered outside the aggregate artifact gate while its proof is in progress.  Its byte-pinned input contains exported function 21, `runMatch` at function 18, the recursive matcher at function 17, and the shared runtime suite at functions 22 through 25.  `ClobLimit.Model.limitL` states the invalid, fully filled, and residual-order branches and inherits the source matcher's natural-number conservation theorem.  The validity subsystem at functions 0 through 6 has an exact artifact theorem and is definitionally equal to the completed `postOnly` subsystem.  The exported invalid branch has an input-generic theorem covering the borrowed book, fresh empty trade array, allocator counters, page count, and below-heap memory frame.  A reusable function-region theorem transports exact interpreter behavior across finite renamings of closed direct-call regions.  A six-function certificate uses it to transfer the owner-aware `matchFuel` search loop and wrapper specifications to limit functions 13 and 14, replacing a third copy of the generated loop proof.  Function 17 has exact termination theorems for zero fuel, zero remaining quantity, and a missing maker, including all five owner-and-pointer results and an unchanged store.  Its separately compiled iteration-control theorem covers the remaining check, owner-aware search, selected-maker quantity read, and full-versus-partial dispatch without elaborating either allocation body.  The full-book, partial-book, and shared trade allocator layouts have exact empty-free-list theorems over the common bump-store semantics, including their complete generated scans and numeric scratch layouts.  The partial-fill book prefix proves all five maker reads, the reduced maker quantity, the source length, and the replacement-book bounds guard in the exact Limit frame.  Its separately compiled control theorem computes the flat-book width and enters an opaque one-result update branch through the shared module-parameterized continuation rule.  The allocator prefix proves the aligned stride-five byte capacity and initializes the exact free-list scan frame.  A separate composition proves the complete empty-list allocation through the shared bump store and exact result frame.  The post-allocation loop proves the counter and length stores, complete payload copy, reconstructed target book, preserved source book, fresh target header, and outside-payload memory frame.  A Limit-specific instruction adapter reuses the shared five-store semantics to prove the updated maker quantity, retained header, outside-payload frame, and returned target pointer.  The generated artifact reproduces byte-for-byte, but the case does not count among the seventeen completed artifacts.

### 5. Consolidate Proof Machinery After Repetition

The CLOB proofs will repeat fixed-width array reads, copy loops, allocation headers, and ownership frames.  Move a pattern into `Project/Common.lean` or the runtime library after two independent cases use the same statement shape and a third case would repeat it.  Keep generated `Program.lean` files untouched and keep artifact-specific address arithmetic near its artifact when no stable general statement exists.

This phase is numbered for accountability but runs during Phases 3 and 4 when the repetition threshold is met.  It must not postpone obvious reuse until all CLOB proofs are complete.  It must also avoid speculative helpers based on one artifact.

- [x] Generalize the fixed-width array predicate used by quote and cancel when the next CLOB proof confirms its shape.
- [x] Generalize fixed-array header preservation across data writes after cancel and `postOnly` established the repeated address form.
- [x] Generalize flat order-word reads and reconstruction of `OrdersAt` after cancel and `postOnly` established the repeated representation.
- [ ] Generalize copy-loop and fresh-array postconditions used by `eraseIdx!`, `push`, and later matching updates.
- [x] Divide the successful `postOnly` branch into separately compiled first-allocation, copy, order-store, and trade-allocation theorems before another append build.
- [x] Generalize one-result branch continuations before a third matcher artifact repeats them.
- [ ] Extend `release_frees_tree` to array-kind nodes, then to shared interior nodes and aliased shared leaves.
- [ ] Reprove `pair_free` and `box_free` as applications of the general teardown library and remove duplicated walk proofs.
- [ ] Add normalizing lemmas or tactics only for address and invariant forms that recur across artifact modules.

`FreshFixedArrayAt.write64_data` proves that an aligned data write at or above a represented fixed array preserves all six header words.  The cancel proof uses it at two write sites, and `AppendOrderCopy` uses it in the successful `postOnly` copy loop.  A combined copy-loop, content, allocation, and memory-frame theorem remains open because cancel copies a prefix and shifted suffix while append copies one flat prefix into a different-capacity array.

`OrderL.word`, `orderWord`, `OrdersAt.orderWord_eq`, and `OrdersAt.ofFlatWords` state the shared relation between flat five-word copies and structured orders.  The cancel proof supplies one indexed field equality for each prefix or suffix branch, while `AppendOrderFinish` reconstructs the appended book from the completed flat prefix and five final stores.  No new tactic is justified while `omega`, `simp`, and `read_frames` discharge the remaining address and read-over-write obligations.

`FixedArrayAllocation` now supplies the shared bump-store transformation and its page, global, and fresh-header facts, together with the recurring bump-root, header-offset, top-minus-one, required-page, memory-size, and no-growth normalizations.  Earlier allocation proofs repeated these calculations for each generated scratch-local layout.  The old `ClobMatchFuel` store name remains an abbreviation, while the Limit proof can depend on the common operation and retain small numeric-layout instruction adapters.

`Project.BranchPost` parameterizes the one-result and nested-result continuation rules by a WASM module.  The completed `matchFuel` proof retains its qualified names through compatibility specializations, while Limit and later artifacts can use the shared definitions directly.  A source rebuild also replaced stale matcher simplifications of the moved bump-store definition with named shared facts or explicit common-definition reductions.

The successful append theorem now contains 229 lines and composes separately compiled allocation, copy, order-finalization, and trade-allocation theorems.  Focused warning-failing builds complete the copy phase in 2.3 seconds, the first allocation in 6.3 seconds, order finalization in 9.4 seconds, the trade phase in 1.7 seconds, and the composed theorem in 14 seconds.  The aggregate `Project.ClobPostOnly.Spec` build also passes after rebuilding the invalid and crossing branches.

This phase ends when allocation-bearing CLOB proofs consume shared semantic lemmas instead of copied instruction walks.  The theorem statements, proof size, and build time provide the acceptance evidence.  A refactor must preserve every artifact theorem and the aggregate proof build.

### 6. Close Diagnostics and Tool Reproducibility

Complete this phase before declaring the next stable point.  Define one CLI error scheme for invalid arguments, unsupported source, I/O failure, and internal inconsistency, with documented nonzero statuses and stderr formats.  Add end-to-end tests for a missing module, missing entry, wrong entry type, unsupported declaration, invalid bound, reserved export name, and failed output write.

Pin every tool that can change generated or decoded artifacts.  Record and enforce the supported Node version, record and enforce the `wasm-tools` version, and verify Wasmtime release archives against checked hashes.  A toolchain change requires full execution and proof gates, artifact-byte review, version and checksum documentation, and trusted-base review.

- [x] Define and test CLI failure categories, exit statuses, stdout use, and stderr context.
- [x] Pin and check Node and `wasm-tools` without adding a package dependency solely for version checking.
- [x] Add checked Wasmtime archive hashes for every supported release artifact and platform.
- [x] Separate cold dependency setup from concise gate summaries so build volume cannot hide a failed comparison.
- [x] Remove the known `AsciiDigits.lean` warning in a focused change that preserves behavior.
- [x] Preserve command, launch, status, signal, and output context when JavaScript test processes fail.
- [ ] Remove proof warnings during substantive proof rebuilds, using focused checks that preserve behavior; defer warning-only elaboration when it exceeds the resource-limited diagnostic timeout.

`Project.Validate.Spec` reached a fifteen-minute constrained timeout after the proof cache was removed.  Earlier unchanged builds of `Project.SharedPair.Spec` and `Project.LebU32.Iter` reached 30-minute and 15-minute limits, while the stale `Project.LebU32.NegIter` target has the same iteration structure.  Substantive work on any of these proofs starts by dividing its long instruction theorem into separately compiled phases.

## Reproducible Gates

| Change | Required checks |
|--------|-----------------|
| Documentation only | `git diff --check`, local-link review, and command review for every changed example. |
| Source example | Targeted Lake build, the relevant execution test, and a standard-Lean comparison when the entry has ordinary source semantics. |
| Diagnostic behavior | Targeted status and stderr assertions, report-classification tests, and `lake build lean-wasm`. |
| Extraction, IR, ownership, ABI, or WASM emission | Targeted fixtures, `node test/run_all.js`, `tools/check-wat.sh`, and `tools/check-talos.sh`. |
| Artifact proof | The per-case script during iteration, `tools/check-talos.sh` before completion, and the source entry's execution test. |
| Toolchain or artifact-producing tool | Full execution and proof gates, artifact-byte review, documented versions and checksums, and trusted-base review. |

The standard comparison runner should gain a quiet summary mode and timing by entry.  Reuse one compiled artifact for repeated inputs only after a trace proves that the cache key includes the module, entry, adapter mode, compiler binary, and ABI bounds.  This maintenance remains secondary unless test duration blocks semantic work.

## Later Work

After the next stable point and after the CLOB helper boundaries stabilize, prove lowering correctness for the scalar fragment shared by `gcd`, `order_book`, CLOB scans, and CLOB decision logic.  The fragment should cover locals, calls, 64-bit operations, conditionals, lets, structured loops, and traps, relating IR evaluation to the Talos execution model.  Existing artifact theorems remain the shipping guarantee while this theorem reduces repeated instruction proofs.

The representation choice requires discussion before implementation.  A direct translation from the compiler's structured `Wasm.Instr` and module values to Talos values permits a universally quantified theorem, while byte-pinned artifact checks continue to connect generated binaries to decoded shipped code.  The proposal must state the additional trusted code, agreement with Talos decoding, and exact supported fragment before adding the boundary.

## Completion Criteria

This plan reaches its next stable point when runtime-intrinsic semantics are explicit, every accepted release has a checked direct-handoff justification, matched values evaluate once, and CLOB `cancel`, `findBest`, `postOnly`, `matchFuel`, `limit`, `market`, and `depth` have input-generic Talos theorems tied to shipped bytes.  The execution suite, WAT round trip, ownership checks, CLI failure tests, and all artifact proofs must pass with enforced Node, `wasm-tools`, Lean, Talos, and Wasmtime versions.  The specification, manual, developer guide, proof inventory, plan, and journal must agree with the implementation and state the evidence supporting each claim.
