# Strategies for Talos Artifact Proofs

These notes describe proof strategies that recur in the checked Talos artifact proofs.  They concern the `Program` produced from exact WASM bytes and the `Wasm.TerminatesWith` or weakest-precondition theorem proved about that program.  The [proof-engineering journal](plan-notes.md), the [proof-library plan](wasm-proofs.md), and the checked modules cited below supply the evidence for each recommendation.

The document serves two readers.  A person can read it as a guide to the proof architecture, while `leanexegen` can select marked sections as optional context for its artifact-proof task.  The section text supplies strategies and examples, but the generated Lean proof and every imported Lean declaration remain subject to kernel checking.

## Scope and evidence

The strongest evidence comes from completed proofs with different control-flow and memory shapes.  [`Project.Validate`](../proofs/talos/lean/Project/Validate/Spec.lean) proves a byte-scanning loop with calls and a folded 24-slot local frame, [`Project.ClobFindBest`](../proofs/talos/lean/Project/ClobFindBest/Spec.lean) proves a search over a represented order array, and [`Project.ClobMatchFuel`](../proofs/talos/lean/Project/ClobMatchFuel/Correct.lean) proves a stateful matching loop with allocation, release, ownership, free-list, and counter obligations.  [`Project.ClobDepth`](../proofs/talos/lean/Project/ClobDepth/Spec.lean) adds stride-two array reconstruction, copy invariants, and reusable allocation adapters, while [`Project.LebU32`](../proofs/talos/lean/Project/LebU32/Spec.lean) records the cost of dividing a large encoder proof at loops and allocation phases.

The current array-based prime-factor demo supplies provisional evidence about a smaller generated artifact.  Its proof draft separates number-theoretic facts from two generated loops, models loop runs as inductive relations, and proves uniqueness when the artifact repeats a computation.  At the review on 2026-08-03, that draft had not reached an accepted public artifact theorem, so it informs strategy selection without serving as acceptance evidence.

Three categories must remain distinct.  A strategy note tells the proof agent how to organize a proof and contributes no Lean declaration.  Application mathematics, such as a theorem about prime-factor counts or order-book priority, belongs in the generated behavior module or a frozen formal module and enters the theorem through that checked source.  A shared lemma or tactic, such as `Project.ProofKit.Control.wp_entry` or `Project.Common.read64_write64_ne`, enters the Lean import closure and therefore requires the repository's import, identity, and axiom checks.

The current `leanexegen` allowlist admits `Project.ProofKit.Memory`, `Project.ProofKit.Array`, `Project.ProofKit.Allocation`, and `Project.ProofKit.Control` but excludes the other `Project` modules cited here.  Those citations document successful proof shapes and candidate shared results, rather than granting the generated proof permission to import them.  Codex must prove every remaining case-local fact from the generated modules or permitted Talos, Mathlib, or core declarations.

## Selection from `Program`

<!-- leanexegen-section:strategy.core begin -->
<a id="strategy-core"></a>
### `strategy.core`: choose the proof architecture from the artifact

Start with the reachable functions in `Program`, beginning at the exported function index named by `ArtifactSpec`.  Record each reachable function's calls, loops, branches, local count, globals, loads, stores, and memory-growth instructions before writing semantic lemmas.  This inventory determines the proof order and prevents a source-level account from replacing the artifact's control flow.

Prove leaf functions before callers, loop bodies before wrappers, and semantic state transitions before long instruction sequences.  Divide one generated function at calls, block-wrapped loops, large branches, allocation phases, copy phases, final stores, and result construction.  Each division should use a named instruction list or an extraction from `Program` whose equality with the generated slice reduces by `rfl`.

State a strong postcondition at every division.  The postcondition should name the returned values, store changes, preserved regions, and local values needed by the next region.  A weak existential postcondition often forces the caller to replay the callee's instruction proof because it omitted one store or representation fact.

The final public proof should contain little discovery.  It resolves the export, introduces the quantified host, store, pointer, input, and precondition, then composes the function theorems already proved.  The [CLOB matcher entry proof](../proofs/talos/lean/Project/ClobMatchFuel/Entry.lean) and [final correctness composition](../proofs/talos/lean/Project/ClobMatchFuel/Correct.lean) show this bottom-up order at a larger scale.
<!-- leanexegen-section:strategy.core end -->

The routing table gives each marked section a stable identifier.  A selector should match features over the export-reachable call graph, since unreachable helper functions should not enlarge the task context.  Selection may include extra advice when classification remains uncertain, but it must record the feature and rule that selected every section.

| Program or theorem feature | Select | Reason |
|---|---|---|
| Every artifact proof | `strategy.core`, `strategy.diagnostics` | Establish the decomposition order and bounded iteration process. |
| Direct or indirect `.call` | `strategy.calls` | Prove callees once and compose their termination theorems. |
| `.loop`, back-edge `.br`, or a block-wrapped loop | `strategy.loops` | Supply invariant, measure, body, and exit design. |
| At least 16 locals, repeated `localGet`/`localSet`, or a loop | `strategy.frames` | Keep generated local arrays folded and expose semantic fields. |
| `addI64`, `subI64`, `mulI64`, division, remainder, or unsigned comparison | `strategy.arithmetic` | Stage wrap bounds and convert machine arithmetic to `Nat`. |
| The fixed `Array UInt64` interface or indexed payload loads | `strategy.arrays` | Relate length-prefixed memory to logical arrays. |
| Reachable allocator template, `memoryGrow`, allocator globals, or fixed-array header stores | `strategy.allocation` | Separate bump, fit, growth, free-list, and release cases. |
| Any load or store | `strategy.memory` | Prove access bounds, address normalization, and read/write frames. |
| A reachable function exceeds 200 instructions, uses at least 32 locals, contains nested loops, or a proof attempt stalls | `strategy.elaboration` | Reduce the theorem boundary before repeating an expensive check. |

The selector should scan instruction constructors rather than WAT text.  It should compute a call graph from the frozen `Program`, attach instruction counts and local counts to each reachable function, and emit the facts used for routing.  Template recognition for allocation should remain conservative and versioned because raw function indices and generated local indices can change between artifacts.

## Control flow

<!-- leanexegen-section:strategy.calls begin -->
<a id="strategy-calls"></a>
### `strategy.calls`: helper functions and call boundaries

Give every reachable helper a theorem over its semantic arguments.  A pure helper should return an exact value and preserve the store, while a memory helper should state its precise store transformation and frame.  The scalar theorems in [CLOB find-best helpers](../proofs/talos/lean/Project/ClobFindBest/Helpers.lean) exemplify the pure form: each theorem exposes a logical predicate such as eligibility and proves `st' = st`.

At a call site, execute only to the call, apply the callee's `TerminatesWith` theorem through `Wasm.wp_call_tw`, introduce the returned store and values, and continue from the callee's semantic postcondition.  Check the generated operand order in `Program`, since WebAssembly stack order often reverses the apparent parameter order in the theorem arguments.  Keep the call theorem's store postcondition strong enough to preserve every memory representation and global needed after the call.

A wrapper that performs straight-line setup, makes one call, and returns the call result has a stable shape.  The checked [`wp_entry_single_call`](../proofs/talos/lean/Project/ProofKit/Control.lean) tactic handles that shape when its structural reductions match, while the [proof-kit catalog](../proofs/talos/lean/Project/ProofKit/README.md) states its syntax and obligations.  If the tactic fails to match, use the explicit `wp_call_tw` sequence because a failed structural tactic says nothing about the callee theorem.

Recursive or mutually dependent generated helpers require a different boundary.  Look for an emitted fuel parameter or another well-founded state, state the helper theorem by induction on that value, and expose a call theorem whose postcondition no longer mentions the recursive instruction body.  Avoid unfolding a proved helper in its callers, since that duplicates both semantic work and elaboration cost.
<!-- leanexegen-section:strategy.calls end -->

<!-- leanexegen-section:strategy.loops begin -->
<a id="strategy-loops"></a>
### `strategy.loops`: invariants, measures, and exits

A useful loop invariant combines four kinds of facts: the application relation, the represented memory, the generated local frame, and the store frame.  State the relation between the current accumulator and the final mathematical answer before adding local indices.  The byte validator's [`vInv`](../proofs/talos/lean/Project/Validate/Invariant.lean) carries either a scanned prefix or a completed answer, while the matcher's [`RunningFacts`](../proofs/talos/lean/Project/ClobMatchFuel/LoopInvariant.lean) carries the source transition, owned arrays, free list, globals, memory frame, and remaining allocation budget.

Choose a measure that decreases on every generated back edge, including administrative passes through a done flag.  A plain fuel value works only when each repeat decrements it.  The validator uses `2 * fuel + done-bit`, and the matcher uses `2 * fuel + 1` for running states and zero for completed states, so a completion transition can repeat once without violating well-foundedness.

For a fixed-count construction loop, define the measure from the generated counter local rather than equality with the complete local frame.  Operand-stack changes can make whole-frame equality unsuitable even when the persistent counter still determines progress.  Prove the counter getter at invariant entry and its strict decrease on the repeat branch.

Some loops have two kinds of progress.  A trial-division loop can reduce the remaining dividend or advance the divisor while leaving the dividend unchanged, so a lexicographic measure encoded as `remaining * 2^64 + (2^64 - divisor)` matches those two transitions.  The live prime-factor draft uses this form, but its public artifact proof was incomplete at the time of review and the measure still requires acceptance through Lean.

Prove invariant initialization, one semantic transition per branch, strict measure decrease, and exit interpretation as separate facts when any one becomes substantial.  The [CLOB matcher loop](../proofs/talos/lean/Project/ClobMatchFuel/Loop.lean) delegates guard behavior and dispatch behavior to named modules, then applies the Talos loop rule to the combined invariant.  This division keeps the loop theorem focused on the control rule instead of allocator arithmetic or application transitions.

Use a postcondition-generic loop-body theorem when Talos exposes a large match continuation.  [`Project.Common.wp_loop_body_intro`](../proofs/talos/lean/Project/WpScaffold.lean) converts a body theorem with explicit trap, repeat, fallthrough, and break premises into the continuation required by `Wasm.wp_loop_cons`.  This pattern prevents a large outer postcondition from becoming part of every instruction-level body goal.

Operational trace relations can help when generated code runs the same deterministic loop more than once.  Define an inductive relation with one constructor per loop branch, prove that two runs from the same start have the same result, and connect each instruction branch to one constructor.  The prime-factor draft uses `EvenRun` and `TrialRun` this way to equate an original run with a later recomputation, while keeping the number-theoretic invariant separate.

The checked proof kit can remove the entry and block boilerplate without choosing an invariant.  [`wp_entry_to_loop`](../proofs/talos/lean/Project/ProofKit/Control.lean) reaches the block-wrapped loop, and `wp_block_loop` applies the block and loop rules with caller-supplied invariant and measure.  These tactics help only when `Program` has the documented shape, and the generated proof retains every invariant, preservation, decrease, and exit obligation.
<!-- leanexegen-section:strategy.loops end -->

## State representation

<!-- leanexegen-section:strategy.frames begin -->
<a id="strategy-frames"></a>
### `strategy.frames`: locals and operand stacks

Generated functions can have dozens of locals, but most proof regions use a small subset.  Define a semantic record for named registers when many regions update the same generated frame, or define a predicate over `Locals.get` when only selected slots carry meaning.  The prime-factor draft uses a `Registers` record and a single `frame` function, while [`LoopLocalsAt`](../proofs/talos/lean/Project/ClobMatchFuel/LoopInvariant.lean) records selected getter facts for a 76-local matcher frame.

Keep large local arrays folded during instruction stepping.  The [`frame_step` declarations](../proofs/talos/lean/Project/Validate/Frame.lean) state generated get, set, length, and refolding equalities, and [`wp_run_folded`](../proofs/talos/lean/Project/WpScaffold.lean) uses only that dedicated simplification set.  The proof-engineering journal reports that this change reduced the `Project.Validate.Loop` build from 1,560 seconds to 15 seconds, which makes folded frames the established response to repeated reduction of literal local lists.

Separate operand-stack traffic from persistent local state.  Talos updates `Locals.values` while instructions execute, so frame lemmas should show that getters and validity ignore stack changes and that setters preserve the current value stack.  `Project.WpScaffold` supplies these neutral facts, allowing a semantic frame to remain folded while `wp_run_folded` processes stack operations.

State exact frame equalities at region boundaries.  A theorem that takes an abstract `base : Locals` should require its parameter length, local length, empty value stack, and the few indexed values it reads.  The [empty free-list search adapter](../proofs/talos/lean/Project/ClobDepth/MissingSearch.lean) follows this pattern and works for both branches that share the same generated search sequence.

Use `change`, `show`, or a small `suffices` statement to refold a frame after executing a region.  Broad simplification of a record and its full local list can destroy the abstraction just before the next theorem expects it.  The boundary equality should mention the exact record update or frame constructor that the following theorem accepts.
<!-- leanexegen-section:strategy.frames end -->

<!-- leanexegen-section:strategy.arrays begin -->
<a id="strategy-arrays"></a>
### `strategy.arrays`: fixed arrays and the public ABI

The `leanexegen` ABI represents an `Array UInt64` by a pointer to an eight-byte length followed by eight bytes per element.  `FormalSpec.UInt64ArrayAt` supplies the whole-region bounds, the length read, and one indexed read equation for every logical element.  Split those components once near function entry, then derive named load bounds and address equalities for the exact indices used by `Program`.

The checked [`Project.ProofKit.Array`](../proofs/talos/lean/Project/ProofKit/Array.lean) module performs this decomposition once.  Change a generated `FormalSpec.UInt64ArrayAt` hypothesis to `Project.ProofKit.UInt64Array.At`, then use `lengthRead`, `elementRead`, `lengthBound`, `elementBound`, `pointerAddress_eq`, `elementAddress_eq`, and `encodedSize_eq_one` instead of repeating address and encoded-length arithmetic.  The [proof-kit catalog](../proofs/talos/lean/Project/ProofKit/README.md) gives the exact singleton, pair, frame, and nested-write recipes supplied to every proof task.

Keep the ABI payload predicate separate from the LeanExe owned fixed-array representation.  The payload theorem needs the length and element words visible from the returned pointer, while `FreshFixedArrayAt` also describes six allocator header words before that pointer.  Allocation proofs often need the stronger owned representation internally and can project the ABI payload facts only in the public postcondition.

For a fixed input length, avoid an artificial semantic loop.  Prove that the length word selects the fixed-size branch, instantiate the indexed read premise at each required index, and execute the unrolled loads in their generated order.  A fixed ten-pair association list therefore needs one query word and twenty key/value words, with the theorem deriving each read from the same `UInt64ArrayAt` premise.

Represent structured elements through a small logical model rather than repeated address expressions.  [`LevelsAt`](../proofs/talos/lean/Project/ClobDepth/Representation.lean) maps pairs of flat words to price and quantity fields, provides indexed and flattened read theorems, and reconstructs the complete representation through `ofFlatWords`.  The same pattern applies to key/value pairs: define the logical pair sequence, prove field reads at `2 * i` and `2 * i + 1`, and keep lookup semantics over that sequence.

The result proof should identify the output pointer after allocation, prove the length word, and prove each result element.  Use `uint64_array_singleton` or `uint64_array_pair` for fixed results, followed by `word_reads` when the final memory is a nested sequence of word writes.  For a variable-size result or a copy, use a prefix invariant and reconstruct the array representation at loop exit.
<!-- leanexegen-section:strategy.arrays end -->

## Arithmetic and memory

<!-- leanexegen-section:strategy.arithmetic begin -->
<a id="strategy-arithmetic"></a>
### `strategy.arithmetic`: stage machine arithmetic before execution

Separate application mathematics from machine arithmetic.  First prove the mathematical transition over `Nat`, lists, or a domain structure, then prove the `UInt64` expression implements that transition under explicit no-wrap bounds.  The prime-factor draft follows this order with lemmas about `primeFactorsList`, then `TrialInvariant.divide` and `TrialInvariant.advance`, before it proves either generated loop.

Convert `UInt64` comparisons to `toNat` form only after recording the bounds that remove modular arithmetic.  [`Project.Common`](../proofs/talos/lean/Project/Common.lean) supplies `u64_eq_iff`, `toNat_add_one`, `toNat_sub_le`, and the `u64_omega` tactic for this sequence.  `u64_omega` expects the relevant `Nat` bounds in context and does not invent a no-wrap premise.

Name the exact equality that connects an emitted expression to a semantic quantity.  The [depth allocation preparation theorem](../proofs/talos/lean/Project/ClobDepth/MissingPrepare.lean) proves the complete rounded-capacity expression equal to `fixedArrayBytesU (levels.length + 1) 2`, rewrites once, and then selects the generated branch.  This directed rewrite is more stable than adding capacity definitions to a large simplifier invocation.

Stage address arithmetic in the same way.  Prove subtraction, addition, and modulo equalities in `Nat`, establish that an address lies below `2^32`, then rewrite the `UInt32` address used by the load or store.  The [validator read theorem](../proofs/talos/lean/Project/Validate/Read.lean) separates the logical byte equation, the bounds check, and the `UInt32` address equality before completing symbolic execution.

Unsigned division and remainder need nonzero-divisor facts before instruction reduction.  Establish those facts from the semantic invariant, rewrite `UInt64.toNat_div` or `UInt64.toNat_mod`, and then use the corresponding `Nat` theorem.  Mixing the divisor proof, generated branch selection, and mathematical transition in one simplifier call makes failures hard to classify.
<!-- leanexegen-section:strategy.arithmetic end -->

<!-- leanexegen-section:strategy.memory begin -->
<a id="strategy-memory"></a>
### `strategy.memory`: loads, stores, and frames

Every load has two independent obligations: the access lies within current memory, and the bytes at that address encode the expected value.  Derive both before stepping the load, using the representation predicate for the value and its region bound.  Normalize the `UInt64` expression, its wrapped `UInt32` address, and the representation's address into one form before applying the read equation.

Every store has a hit fact and a frame fact.  Use `Wasm.Mem.read64_write64_same` for the written word, and use a disjointness theorem for an old read outside the eight-byte window.  [`Project.Common.read64_write64_ne`](../proofs/talos/lean/Project/Common.lean), `read_frames`, and the byte-level `bytes_frames` and `read_frames8` tactics in [`Project.WpScaffold`](../proofs/talos/lean/Project/WpScaffold.lean) encode the checked forms of this reasoning.

Prove separation at the level of regions rather than repeating pairwise address inequalities.  [`LevelsAt.frame_region`](../proofs/talos/lean/Project/ClobDepth/Representation.lean) preserves a source array when another store agrees on the source region, and [`CopyState.advance`](../proofs/talos/lean/Project/ClobDepth/LevelCopyInvariant.lean) combines target writes, source preservation, header preservation, and copied-prefix extension.  These theorems turn a long read-over-write chain into one regional frame premise.

Track page equality and byte equality separately.  Ordinary writes preserve `mem.pages`, while allocation or memory growth can change it under a distinct theorem.  A representation theorem should transport its access bounds through page equality and its contents through byte equality, rather than asserting whole-store equality after a write.

Keep memory transformers named when a region performs several stores.  A definition such as `fixedArrayHeaderMem` or `copyWriteStore` gives later lemmas one stable normal form and prevents the store chain from expanding in unrelated goals.  Prove read-back and outside-region theorems once for that transformer, then use those results in instruction adapters.
<!-- leanexegen-section:strategy.memory end -->

## Allocation and ownership

<!-- leanexegen-section:strategy.allocation begin -->
<a id="strategy-allocation"></a>
### `strategy.allocation`: bump, fit, free-list, and release cases

Determine which allocator branches the formal precondition permits before proving allocator code.  `leanexegen`'s current `RuntimeReady` fixes the free-list head at zero and provides enough existing memory for the result, so an array-construction proof should select the empty-search and no-growth bump branches.  A general free-list theorem adds work that the public precondition cannot exercise.

For the bump case, name the old heap top, allocation size, returned payload pointer, new heap top, and header store.  The checked [`Project.ProofKit.Allocation`](../proofs/talos/lean/Project/ProofKit/Allocation.lean) theorem `bumpFacts` derives the 48-byte header root, post-allocation top, overflow exclusion, no-growth page comparison, and five header-store addresses from the result-region memory bound and WebAssembly page limit.  Apply it before symbolic execution enters the allocator, then use `wordAddress` and `wordAddress_toNat` for returned-array stores instead of deriving their nested `UInt64` and `UInt32` modulo expressions between instruction steps.

When the permitted proof library does not expose the allocator theorem, derive one named eight-byte access bound for every generated header and payload store from the complete result-region bound.  Use those facts to discharge each generated out-of-bounds branch before symbolically executing its store, then collect the store chain in one named memory transformer.  Prove the output length and payload reads from that transformer before entering the result-construction loop.

For a general free list, model search and mutation independently of generated locals.  [`takeFirstFitFrom`](../proofs/talos/lean/Project/Runtime/FreeList.lean) describes selection, and `FreeListAt` supplies node bounds, root separation, remaining-list representation, unlinking, and framing.  The [no-fit search](../proofs/talos/lean/Project/ClobMatchFuel/BookAllocSearch.lean) uses the remaining list length as a measure, while the [fit search and header construction](../proofs/talos/lean/Project/ClobMatchFuel/BookAllocFit.lean) divide the selected node from the skipped prefix and preserve the remaining list through six header writes.

Allocation branches should converge on one semantic result shape.  Both fit and bump results need a fresh header, sufficient capacity, the selected payload pointer, preserved source representations, page facts, allocator globals, and an outside-region frame.  Branch-specific origin facts can remain behind that common result so later copy and store phases do not split again.

Release changes ownership, free-list links, and counters together.  The wrapper theorem [`func18_frees_fixed_array_zero_mask`](../proofs/talos/lean/Project/ClobMatchFuel/Allocation.lean) instantiates the shared runtime release theorem for an artifact function and states exact memory and global transformers.  Keep the refcount test, payload destruction policy, free-list insertion, and global counter changes explicit because later allocation may depend on each one.

Budget arithmetic belongs in the loop invariant when every iteration allocates.  The matcher invariant bounds the heap top plus remaining fuel times a per-step byte budget, which discharges each later bump allocation without rebuilding a global estimate.  A fixed-size result needs a smaller premise: enough room for one header and its fixed payload, already provided by `RuntimeReady` in current `leanexegen` specifications.
<!-- leanexegen-section:strategy.allocation end -->

## Proof construction and diagnosis

<!-- leanexegen-section:strategy.elaboration begin -->
<a id="strategy-elaboration"></a>
### `strategy.elaboration`: control theorem size

Treat elaboration cost as evidence about the proof boundary.  If Lean spends substantial time reducing instructions without presenting a local goal, divide the program at the nearest call, loop, branch, allocation phase, copy phase, or store suffix.  The repository instructions prohibit repeating an unchanged target after a timeout without a diagnostic, and the proof-engineering journal records the same response.

Keep weakest-precondition lemmas generic over the remaining program and postcondition when composition needs that generality.  A common form takes `rest`, `Q`, and a hypothesis proving `wp module rest Q` from the semantic exit frame, then proves `wp module (region ++ rest) Q` from the entry frame.  This continuation-passing shape lets the next module decide the final property without making the region theorem elaborate a large outer assertion.

Avoid large conjunction construction in a goal that still contains an expensive `wp` term.  Prove a compact semantic structure or conjunction first, then attach the continuation with a small theorem such as [`and6_and`](../proofs/talos/lean/Project/Common.lean).  The same principle applies to loop continuations: move the large match behind `wp_loop_body_intro` or a compact intermediate assertion.

Prefer `simp only` with named frame facts to broad `simp`, and use directed `rw` for representation changes.  A local `wp_run_*` macro should cover one short instruction region and list only the definitions needed for that region.  Raising heartbeat or recursion limits can accommodate a bounded theorem after decomposition, but it does not repair a boundary that repeatedly unfolds a large program or local frame.

Control asynchronous elaboration for modules whose proofs retain large terms.  Several established heavy modules use `set_option Elab.async false in` around one theorem so resource behavior remains predictable under the repository's single-process Lean runner.  Apply this only after the theorem has a semantic boundary, since serialization does not reduce its term size.
<!-- leanexegen-section:strategy.elaboration end -->

<!-- leanexegen-section:strategy.diagnostics begin -->
<a id="strategy-diagnostics"></a>
### `strategy.diagnostics`: iterate from the first semantic mismatch

Run the exact build command supplied by `leanexegen` after each coherent edit and inspect the first unsolved goal or error.  Classify the failure before changing tactics: semantic gap, representation gap, arithmetic presentation gap, instruction adapter gap, elaboration boundary failure, or artifact change.  The classification determines whether the next edit belongs in an application lemma, representation theorem, arithmetic equality, short `wp` adapter, or smaller module.

A semantic gap means the generated state is understood but no theorem states the needed application, allocator, or ownership transition.  A representation gap means reads or writes are available but the proof cannot reconstruct or preserve the logical value.  An arithmetic presentation gap means equivalent addresses, capacities, counters, or lengths occur in incompatible syntactic forms.

An instruction adapter gap appears when the semantic theorem exists but generated locals or an instruction slice do not match it.  Prove an exact frame equality or a short continuation-generic region theorem, then retry the semantic application.  An elaboration boundary failure appears when Lean consumes time or memory before producing a useful local goal, which calls for a smaller theorem rather than another unchanged run.

An artifact change invalidates `rfl` decompositions and local-index assumptions.  Compare the frozen `Program`, function table, call graph, and instruction regions before editing semantic proofs.  Do not weaken an exact decomposition to accommodate two different artifacts, since each artifact theorem concerns one decoded byte sequence.

Use temporary `#check` or `#print` commands only inside the prescribed proof workspace and remove diagnostic declarations from the final behavior module.  Confirm unfamiliar checked lemmas against their current signatures, especially implicit module, function index, store, and continuation parameters.  The outer `leanexegen` check remains authoritative after the proof agent reports success.
<!-- leanexegen-section:strategy.diagnostics end -->

## What belongs where

Reusable strategy concerns the order and shape of proof work.  It includes call-graph order, continuation-generic region theorems, four-part loop invariants, folded frames, staged arithmetic, representation reconstruction, and failure classification.  These ideas may appear in task notes without changing the theorem's Lean dependencies.

Application mathematics states why the algorithm computes the requested function.  Prime-factor list transitions, best-order properties, association-list lookup semantics, and matching-state transitions belong with the generated case unless two independent artifacts use the same theorem.  The proof agent must prove or import these facts in Lean, and prose advice cannot discharge them.

Checked library material implements semantic facts or mechanical proof steps.  [`Project.ProofKit.Control`](../proofs/talos/lean/Project/ProofKit/Control.lean) contains small structural tactics, [`Project.Common`](../proofs/talos/lean/Project/Common.lean) contains arithmetic and memory lemmas, and the [runtime modules](../proofs/talos/lean/Project/Runtime/Spec.lean) contain allocator, retain, release, and ownership results.  Importing one of these modules changes the theorem dependency closure and requires an explicit allowlist plus transitive source identity.

Promote a case-local theorem only when its statement depends on stable semantics rather than one generated local layout.  The existing policy asks for two independent consumers unless the theorem states a direct fact about pinned Talos semantics.  Tactics should normalize repeated syntax, while ownership, allocation meaning, application transitions, and invariant premises remain visible in theorem statements.

## Supplying optional notes to `leanexegen`

The marked sections support deterministic extraction.  Each block begins with `leanexegen-section:<id> begin` and ends with the matching marker, and the routing table defines its feature predicate.  Leanexegen rejects duplicate identifiers, unmatched markers, and a block whose heading identifier differs from its marker.

The proof-task workspace receives two context files.  `PROOF_STRATEGIES.md` contains an import warning followed by the feature-selected sections in document order.  `PROOF_TASK_FEATURES.json` contains the export index, reachable call graph, per-function instruction and local counts, selected identifiers, and the rule that selected each identifier, while the prompt identifies the notes as optional guidance.

The selector includes `strategy.arrays` for the fixed public ABI, `strategy.allocation` for a reachable memory-growth instruction or the current allocator-global and store signature, and `strategy.memory` for any load or store.  Call, loop, frame, arithmetic, and elaboration selection follows the routing table.  Classification reads only the frozen `Program`; it does not consult the prose request or generated Source.

Selection distinguishes generation provenance from theorem dependencies.  Package schema 4 archives the extracted notes, feature manifest, source-document digest, and extractor version, allowing a later audit to reconstruct the proof agent's context.  Independent Lean verification does not import these files or require the checkout's prose to match, because the accepted `Behavior.lean` contains every proof term that reaches the theorem.

`PROOF_LIBRARY.md` has a different role.  It catalogs checked declarations that Codex may import, and an imported proof-kit tactic contributes to elaboration of the checked proof and to the verifier-source identity.  Leanexegen presents the library catalog and strategy notes as separate files, and the retained `Behavior.lean` records which allowed modules the final proof imported.

A controlled `reprove` experiment can measure whether the notes help.  Hold the formal specification, `Program`, WASM bytes, deterministic artifact modules, toolchain, and proof-kit availability fixed, then regenerate only `Behavior.lean` with and without selected strategy sections.  Compare acceptance, proof text, imported modules, stage-five duration, failed build count, and the semantic decomposition used, while treating one run as evidence for that artifact rather than a general performance result.

## Limitations and failure modes

Program-feature routing cannot infer the application invariant.  It can identify a loop with division and remainder, but it cannot decide that prime-factor list length is the right accumulator relation.  Codex still has to connect the frozen formal specification to the artifact's machine state through checked mathematics.

Generated syntax changes can invalidate structural tactics, instruction slices, and local-frame lemmas while preserving broad algorithm behavior.  A proof strategy should fail at an exact `rfl`, call, or frame boundary in that case.  A permissive tactic that continues after the mismatch risks spending substantial time on the wrong control-flow shape.

Memory and allocation advice depends on explicit preconditions.  An empty free-list and sufficient existing pages justify the bump-only path, while a weaker `RuntimeReady` would require fit, no-fit, and growth cases.  Reusing an allocator theorem without its separation, bounds, page, global, or ownership premises leaves a real semantic gap.

Fixed-array advice currently covers flat `UInt64` payloads and the established LeanExe header model.  Nested arrays, variable-width elements, aliases, shared ownership, and host references require additional representation predicates and frame theorems.  The routing mechanism can select a memory section for those artifacts, but these notes do not supply the missing semantics.

Large selected contexts can hinder proof generation.  The selector should prefer the smallest closed set of relevant sections, while selecting the elaboration section before the session when the static complexity rule matches.  Controlled reproofs that hold the artifact and all checked inputs fixed should evaluate selection quality.

The notes can become stale as Talos, LeanExe, or the checked proof library changes.  Local links and cited declarations should receive a documentation test, and the extractor should bind each generated context to the source-document digest.  Lean's kernel, the import audit, the axiom audit, and exact-artifact validation remain the acceptance mechanisms even when every strategy recommendation is current.
