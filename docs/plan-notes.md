# Proof Engineering Plan Notes

This document records techniques and candidate lemmas that can reduce the cost of the proof work in the [development plan](../plan.md).  It is a working companion to the plan rather than a second work queue: `plan.md` owns required results and their order, while this document owns proof structure, reusable assets, failed approaches, and proposed improvements.  Update it when a proof confirms a reusable pattern, reveals that an apparent pattern differs materially, or establishes a better elaboration boundary.

The current emphasis is the input-generic `clob_depth` artifact proof.  Its two level-update allocation branches repeat allocator and copy behavior already proved for order and trade arrays, but use stride-two level data and different generated local indices.  The notes below distinguish direct theorem reuse from examples that still need an artifact-specific adapter.

## General Method

State the semantic result before reducing generated instructions.  Define the source model, the memory representation, exact read and reconstruction lemmas, ownership, and memory-frame statements first.  The instruction proof should then transform one explicit semantic frame into the next rather than discover the semantic statement while simplifying a large generated program.

Divide a generated function at calls, loops, branches, allocation phases, copy phases, final stores, and result construction.  Each region should have an explicit instruction list or a small extraction whose decomposition against the generated function is proved by `rfl`.  A theorem for one region should expose only the locals and store facts needed by the following region.

Keep generated local-index manipulation in artifact modules.  Shared modules should describe semantic memory transformations, arithmetic facts, ownership preservation, copy results, and branch composition without referring to one artifact's local numbers.  This division allows another artifact to reuse the hard memory theorem while proving a short adapter for its generated frame.

Prefer explicit equalities and directed rewriting over broad simplification.  A capacity expression, address normalization, or counter formula should receive a named equality and be rewritten at the exact boundary where the generated expression meets the semantic frame.  Large `simp` invocations over dozens of instructions can normalize unrelated definitions, obscure the remaining mismatch, and consume excessive elaboration resources.

## Current Asset Inventory

The existing library covers every major semantic obligation in a fixed-array allocation.  Some theorems are parameterized by stride and apply to depth directly, while order- and trade-specific preservation theorems provide small patterns for level-specific wrappers.  The missing-price branch now has depth adapters for search, bump allocation, copying, and appended stores, while the found branch still needs its generated-local adapters.

| Obligation | Existing asset | Reuse classification | Depth use |
|------------|----------------|----------------------|-----------|
| Capacity calculation | [`fixedArrayBytesU_toNat` and `fixedArrayBytesU_round`](../proofs/talos/lean/Project/Clob.lean) | Direct | Normalize `8 + n * 2 * 8`, prove no wrap, and eliminate redundant rounding. |
| Preparation instructions | [Limit book-allocation preparation](../proofs/talos/lean/Project/ClobLimit/InternalPartialBookAllocPrepare.lean) and [matcher allocation preparation](../proofs/talos/lean/Project/ClobMatchFuel/BookAllocPrepare.lean) | Close example | Copy the named complete-capacity equality and final-frame equality pattern, changing stride and local indices. |
| Free-list model | [`takeFirstFit`, `takeFirstFitFrom`, and `FreeListAt`](../proofs/talos/lean/Project/Runtime/FreeList.lean) | Direct | State the selected node, remaining list, capacity bound, unlink behavior, and no-fit condition. |
| Free-list instruction loop | [Book allocation search](../proofs/talos/lean/Project/ClobMatchFuel/BookAllocSearch.lean) and [fit branch](../proofs/talos/lean/Project/ClobMatchFuel/BookAllocFit.lean) | Adapter required | Reuse the invariant and semantic lemmas with depth's local frame and stride two. |
| Fit allocation memory | `fixedArrayAllocFitMem`, `fixedArrayAllocFitStore`, `freeListAt_fixedArrayAllocFitMem`, and `freshFixedArrayAt_fixedArrayAllocFitStore` in [Book allocation fit](../proofs/talos/lean/Project/ClobMatchFuel/BookAllocFit.lean) | Direct semantic reuse | Produce a fresh stride-two header and the remaining represented free list. |
| Bump allocation memory | [`fixedArrayAllocBumpStore` and its facts](../proofs/talos/lean/Project/FixedArrayAllocation.lean) | Direct | Establish the fresh header, new heap top, unchanged pages, preserved globals, and bytes below the old heap top. |
| Bump instructions | [Book bump allocation](../proofs/talos/lean/Project/ClobMatchFuel/BookAllocBump.lean) | Adapter required | Reuse the proof sequence with depth's locals and a stride-two header store. |
| Fresh header preservation | [`FreshFixedArrayAt.write64_data` and frame theorems](../proofs/talos/lean/Project/Clob.lean) | Direct | Preserve the six metadata words while writing length and level data. |
| Level representation | [Depth level-array representation](../proofs/talos/lean/Project/ClobDepth/Representation.lean) | Direct | Read flat level words, prove their bounds, reconstruct `LevelsAt`, frame an owned input region, and preserve a source representation across disjoint target writes. |
| Level-copy transition | [Shared level-copy invariant](../proofs/talos/lean/Project/ClobDepth/LevelCopyInvariant.lean) | Direct for depth branches | Parameterize target length and payload size while preserving the source, fresh header, copied prefix, pages, globals, and outside-target bytes. |
| Append copy | [Missing-price copy invariant](../proofs/talos/lean/Project/ClobDepth/MissingCopyInvariant.lean), [instruction loop](../proofs/talos/lean/Project/ClobDepth/MissingCopy.lean), and [final-store facts](../proofs/talos/lean/Project/ClobDepth/MissingStoreFacts.lean) | Implemented depth adapter | Copy all old level words, preserve the source and fresh target header, frame writes, and reconstruct `levels ++ [newLevel]`. |
| Same-length copy | [Book replacement copy](../proofs/talos/lean/Project/ClobMatchFuel/BookReplaceCopy.lean) | Close example | Copy every level word and reconstruct the original level list before changing the matched quantity. |
| Field replacement | [Book replacement stores](../proofs/talos/lean/Project/ClobMatchFuel/BookReplaceStore.lean) | Close example | Preserve prices and unrelated quantities while replacing one quantity word. |
| Input memory frame | `fixedArrayHeaderMem_bytes_before`, `fixedArrayAllocFitMem_bytes`, and `LevelsAt.frame_region` | Mostly direct | Preserve the input level array across either allocation result and all writes to a disjoint target. |
| Page and global facts | Fixed-array allocation page and global theorems, plus allocator frame theorems | Direct | Preserve pages and unrelated globals and state the exact heap-top or free-head change. |
| Allocation counter | Completed `postOnly`, `matchFuel`, and `limit` allocation branches | Close example | Prove the generated global-two increment after either fit or bump allocation. |
| Read-over-write normalization | [`read_frames` and memory arithmetic](../proofs/talos/lean/Project/Common.lean) | Direct | Close disjoint header, source, and target read obligations after their addresses are normalized. |

The direct assets settle allocator meaning independently of the depth artifact.  The missing append adapter now proves that the generated loop terminates after `levels.length * 2` writes and that the final stores reconstruct the extended represented list.  The found adapter can reuse `LevelsAt.levelWord_eq_flat`, `levelWord_bound_flat`, `ofFlatWords`, and `frame_write64_flatWordsDisjoint`, but it needs a same-length target invariant and an indexed quantity-replacement theorem.

## Immediate Depth Application

The missing-price preparation is divided into a twenty-instruction field phase and a twenty-four-instruction allocation phase.  `MissingFields.missingFieldsProg_spec` proves the field phase and its target-length arithmetic.  `MissingPrepare.missingPrepareProg_spec` proves the allocation phase, including the rounded capacity, minimum-capacity branch, zeroed scratch locals, and initial free-list cursor.

The existing limit preparation proof supplied the exact repair pattern.  The completed depth proof names an equality whose left side is the complete expression emitted by the instruction sequence and whose right side is `fixedArrayBytesU (levels.length + 1) 2`, proves it through `fixedArrayBytesU_round`, and rewrites before selecting the false branch of the minimum-capacity conditional.  A second explicit reduction selects the empty generated branch before the final global read, and the focused warning-failing build passes in 1.4 seconds without a larger simplifier or resource budget.

The missing branch has independently compiled search, bump, allocation-finish, copy, and final-store theorems.  `MissingBranch.missingProg_spec` connects their frames and returns the owned extended level array, exact contents, allocator globals, page equality, owned source, and below-heap byte frame.  The found branch is now the active boundary and must repeat the allocation division for a same-length target and one indexed quantity replacement.

| Depth proof unit | Existing support | Current state | Next semantic result |
|------------------|------------------|---------------|----------------------|
| Missing field preparation | Depth scan and representation | Complete; 1.4-second focused build | Exact target length and word counts. |
| Missing allocation preparation | Capacity arithmetic and prior preparation examples | Complete; 1.4-second focused build | Exact need, scratch locals, and free-list cursor. |
| Missing free-list search | Generic free-list model and empty-search examples | Complete for the stated empty free-list premise; 1.4-second focused build | No-fit state with the prepared frame unchanged. |
| Missing bump branch | Generic bump store and market bump example | Complete; 6.7-second focused build | Fresh stride-two target with exact heap state. |
| Missing allocation finish | Fresh-header, counter, and address facts | Complete; 2.0-second focused build | Target length initialized and allocation count incremented. |
| Missing copy and stores | Depth copy invariant, disjoint-write preservation, and level reconstruction | Complete; 2.0-second final instruction build | `OwnedLevelArrayAt` for `levels ++ [{ price, qty }]`. |
| Missing branch composition | Completed phase theorems and `MissingBranchFacts.ResultState` | Complete; 2.7-second warning-failing build | Exact appended result, allocator globals, owned source, pages, and below-heap frame. |
| Found preparation and allocation | Same allocator assets | Structurally divided | Fresh same-length stride-two target. |
| Found copy and replacement | Replacement-copy examples and `LevelsAt` word API | Not started | Exact list with the first matching level's quantity updated. |
| Per-side fold | Source aggregation properties and completed level update | Not started | Represented levels equal the source fold for one side. |
| Export composition | Owned result predicates and branch composition | Not started | Two owned arrays equal the exact source `depth` result. |

## Candidate Shared Lemmas

Add two level-specific allocator preservation wrappers when the first depth allocation needs them.  One wrapper should preserve `OwnedLevelArrayAt` across a free-list fit allocation using `fixedArrayAllocFitMem_bytes` and `OwnedLevelArrayAt.frame_region`.  The other should preserve it across a bump allocation using `fixedArrayHeaderMem_bytes_before` and the same level frame theorem.

`LevelCopyInvariant.CopyState.advance` now provides the shared stride-two copy transition.  The missing branch instantiates it with target length `levels.length + 1` and payload size `(levels.length + 1) * 2`, while the found branch will use `levels.length` and `levels.length * 2`.  This parameterization removes the repeated memory proof while retaining separate generated-local frames and loop adapters.

The implemented abstraction boundary includes a fresh target header, initialized target length, represented source levels, source and target separation, source word count, target payload size, and equality of the first `k` target words with the source.  Each transition returns the extended copied-prefix relation, unchanged pages and globals, preserved source representation and target header, and bytes outside the target payload.  The artifact-specific theorem retains responsibility for loop termination, generated locals, and final `LevelsAt` reconstruction.

Do not parameterize a shared theorem by arbitrary generated local indices or arbitrary instruction lists.  Such a statement would move elaboration-heavy local manipulation into the common library without removing it.  Keep a small `wp` loop adapter beside each artifact and share the semantic invariant transitions that carry the difficult memory facts.

An allocation-result structure may become useful after the two depth branches are complete.  A candidate structure would distinguish fit and bump origins while exposing the common fresh header, target root and capacity, page facts, allocation counter, free-list result, heap top, and source frame.  Add it only if branch composition repeats the same projections and case split after the depth adapters use the existing theorems.

## Tactics and Elaboration

`read_frames` is the preferred tactic for a finite chain of disjoint memory reads and writes after address equalities are available.  `omega` handles natural-number bounds after `UInt64.toNat` and modular expressions have been rewritten with named no-wrap facts.  `rw` should perform the representation-changing step, while `simp only` should reduce a small, enumerated set of local-frame definitions.

Artifact-local `wp_run_*` macros provide useful records of the definitions required to reduce a generated instruction region.  Their local indices and large simplifier configurations prevent direct reuse, and copying them unchanged can recreate the elaboration problem seen in the initial missing-price preparation theorem.  New depth macros should cover one short region and list only the frame facts required for that region.

Record focused module build time in `devnotes.md` after each completed theorem.  A sharp increase in time, a timeout without a diagnostic, or a simplifier recursion failure calls for a smaller program boundary or a semantic lemma before another build.  Every Lean or Lake invocation remains subject to the repository's cgroup, CPU, priority, timeout, and single-job rules.

## Failure Classification

Classify a failed proof before changing its resource budget or tactic sequence.  The classification determines whether the next action belongs in a semantic library, representation module, arithmetic helper, or artifact adapter.  Record a new recurring class here when two independent proofs exhibit it.

| Failure class | Evidence | Response |
|---------------|----------|----------|
| Semantic gap | The generated state is understood, but no theorem states the required allocator, ownership, or source property. | Prove a small semantic lemma independent of generated locals. |
| Representation gap | Flat memory reads exist, but the proof cannot reconstruct the source object or preserve it through writes. | Add `word`, bounds, `ofFlatWords`, or regional frame facts to the representation module. |
| Arithmetic presentation gap | Two equivalent capacity, address, counter, or length forms prevent theorem application. | Name the exact equality and rewrite at the boundary. |
| Instruction adapter gap | A semantic theorem exists, but the generated local frame or instruction slice does not match it. | Prove a short artifact-local `wp` theorem and explicit frame equality. |
| Elaboration boundary failure | Lean spends substantial time reducing a long program without producing a local goal. | Divide the program or theorem before another run. |
| Artifact change | A formerly exact instruction decomposition or byte comparison fails. | Inspect the compiler, IR, WASM, and generated-program differences before changing the proof. |
| Missing bound | An address, capacity, page, or modular fact cannot follow from current premises. | Derive it from the existing budget or state the necessary semantic precondition explicitly. |

## Maintenance Rules

Update this document in the commit that establishes or rejects a proposed shared lemma.  Move a candidate from discussion to the asset table when a compiled theorem uses it, and record the first two independent consumers.  Remove obsolete proof advice when a new shared theorem replaces the old artifact-specific pattern.

Keep evidence precise.  Name the theorem or module, state whether reuse is direct or requires an adapter, and record focused build behavior in the development journal.  Avoid counting generated lines or theorem count as progress when the remaining semantic obligations differ in difficulty.

Review these notes at each completed depth boundary and before starting another artifact proof.  The review should identify repeated proof code, expensive elaboration, missing representation facts, and assumptions that belong in a public theorem statement.  The goal is a smaller collection of explicit semantic lemmas and short artifact adapters that retain exact ownership, allocator, counter, and memory-frame claims.
