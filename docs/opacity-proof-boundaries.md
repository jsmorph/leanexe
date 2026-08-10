# Opacity and elaboration boundaries in artifact proofs

This file records experiments on reducing Lean elaboration cost in direct WebAssembly proofs.  The immediate source is [Opacity Boundaries for Large Lean Proofs](../../vq/docs/notes/research/lean-opacity-practical.md), which distinguishes checked opacity from compact interfaces and reports cases where generic specification packages removed expensive concrete comparisons.  Each Leanexe experiment records the fixed artifact, the expensive term, the proposed boundary, and the observed result so that a later research note can separate measured results from design hypotheses.

## Research record

Each experiment has a stable identifier and retains enough evidence to reconstruct the comparison.  The record includes the artifact digest and size, generated annotation package, selected LTG entries, initial and final proof, proof journal, Lean diagnostics, Stage 5 telemetry, proof structure and size, and independent package-verification result.  A timeout or rejected design remains part of the record because it identifies the elaboration boundary and prevents a later account from selecting only successful measurements.

The technique ledger distinguishes a checked mechanism from a proposed use and from measured evidence.  A mechanism can improve proof structure while producing an inconclusive or adverse timing result, and one artifact does not establish cross-program reuse.  Promotion into automatically selected LTG support therefore requires exact artifact linkage, an accepted theorem, and evidence from more than one program or a compelling argument that the interface describes a compiler motif rather than application mathematics.

| ID | Technique from the VQ investigation | Leanexe boundary | Evidence and present status |
|---|---|---|---|
| `OPA-001` | Compact opaque theorem with an arbitrary continuation | Demo 9 post-load fold update | Accepted and independently verified.  The theorem removed a heartbeat failure, but the complete run was slower and larger than the retained proof. |
| `OPA-002` | Specification package plus a small semantic accessor | Compiler-described scalar body, condition, and continuing transition | Accepted on Demo 9.  The generated exact WAT-region equality and `guardedBackEdgeProgram_spec` kept the decoded instruction tail outside the loop invariant proof. |
| `OPA-003` | Module split at the expensive semantic boundary | `Project.ProofKit.GuardedBackEdge` and generated `AnnotationMatches` | Accepted on Demo 9.  The first package failed because the module was missing from the canonical proof-kit inventory; the corrected package and independent verifier passed. |
| `OPA-004` | Cross-operation reuse of the same compact package | Demo 10 bounded multiplication fold | Accepted and independently verified on the 1,979-byte artifact with digest `a981c788...d4baa`.  The fresh agent selected the guarded-back-edge entry and applied the generated multiplication, condition, and continuing evaluator equations. |
| `OPA-005` | Inferred internal proposition type | Generated scalar transition accessors | Proposed.  Current explicit accessors quantify over 21 `UInt64` values and produce an 848-character declaration line, but no controlled comparison has tested an inferred alias. |
| `OPA-006` | Local irreducibility | Decoded function and decoded body at public entry | Rejected as a standalone setting, then accepted after a generated dispatch package supplied compact branch and function accessors.  The manual proof passed with `func0` irreducible; a fresh proof-generation measurement remains open. |
| `OPA-007` | Named compact endpoint equality | Generated traversal program, frame, item-validity proof, and continuation theorem | Accepted on Demo 10 in both a manual substitution and a fresh fixed-artifact reproof.  The manual substitution shortened the existing proof, while the fresh proof expanded the generated frame throughout its invariant and was slower and larger. |
| `OPA-008` | Named proposition bridged by consequence | Public artifact postcondition after fixed-store entry conversion | Accepted in the fresh Demo 10 reproof.  Direct `change` failed even when the named definition repeated the generated expressions, while `Wasm.wp.conseq` established the implication and kept the compact name through both length branches. |
| `OPA-009` | Separate compact suffix theorem | Completed fold frame before result placement and the public continuation | Accepted and independently verified on Demo 10.  An inline compact consequence retained the six-gibibyte elaboration failure; a preceding theorem declaration restored diagnostics, and a fresh agent later retrieved and used the generic ProofKit theorem for the same emitted suffix. |
| `OPA-010` | Exact frame equality followed by a continuation-generic helper | Generated traversal and guarded back edge under the complete loop assertion | The artifact-local helper, extracted shared theorem, manual substitution, and fresh fixed-artifact use passed on Demo 10.  A fresh Demo 9 proof retrieved and applied the same theorem to wrapping addition, and independent verification accepted both operations; the Demo 9 run was slower than its guarded-back-edge screen. |
| `OPA-011` | Exact generated accessors for a compact frame | Continuing-frame and result-frame projections used by traversal and singleton-suffix theorems | Generated accessors checked on Demos 9 and 10.  A Demo 9 manual substitution removed ten local projection theorems, reduced the proof from 588 to 555 lines, and passed independent verification; fresh proof-generation time remains unmeasured. |

For each measured run, the notebook records monotonic Stage 5 time separately from Codex time and outer Lean acceptance time.  Proof-size analysis counts lines and explicit scaffolding while treating descriptive declaration names as evidence of shared theorem use rather than complexity.  The proof journal supplies qualitative evidence about retrieval, failed reductions, context compaction, missing lemmas, and the exact residual goals that consumed agent time.

## Technique map

An opaque theorem helps only when its type omits the expanded term that caused the cost.  A theorem whose body is opaque but whose statement repeats a large decoded program, continuation, or concrete local frame still makes every consumer elaborate that expression.  Leanexe therefore needs small semantic endpoints: a named instruction region, a compact post-state description, and an arbitrary continuation or postcondition.

Module boundaries can make those endpoints reusable across artifact proofs.  A shared ProofKit module checks instruction semantics once, while a generated annotation module proves that a decoded artifact interval equals the shared program.  The artifact proof then composes the generated equality with the compiled semantic theorem, leaving program-specific invariants and specification facts outside the expensive instruction reduction.

Inferred proposition types may avoid a second elaboration of a large weakest-precondition expression.  Generated accessors and local `have` bindings can carry the checked proposition without restating its full type, provided that the final public theorem remains explicit and compact.  Local irreducibility may also prevent accidental reduction of a decoded function after entry decomposition, but an experiment must establish that it preserves the explicit reductions required for dispatch and local-frame facts.

## Candidate shared boundary

Leanexe already translates compiler IR expressions and statements into `Project.ProofKit.ScalarTransition` descriptors.  The checked descriptor semantics cover wrapping arithmetic, bitwise operations, shifts, guarded division and remainder, comparisons, conditionals, scratch locals, and assignments.  Reusing this language avoids a new enumeration of fold operations and gives the compiler a structured description of the code it emitted.

The proposed ProofKit interface describes one guarded back edge rather than an entire array fold.  It executes an arbitrary scalar body and Boolean condition, returns `Break 1` when the condition holds, and otherwise executes an arbitrary scalar continuation statement before returning `Break 0`.  Its theorem type refers to `ScalarTransition.State`, the three descriptors, their evaluator results, and an arbitrary postcondition; it does not contain the enclosing array traversal, allocator, result construction, or public specification.

The compiler adds its existing post-test scalar descriptor to an array-fold annotation when `ScalarDescriptor.PostTest.ofIR` accepts the body.  The annotation consumer identifies the exact loop-tail interval and emits a Lean equality between those decoded instructions and the generic guarded-back-edge program, using the index increment as the continuation statement for a forward fold.  Older annotation documents remain valid without the optional descriptor fields, and recipes advertise the theorem only after the exact interval equality succeeds.

This boundary turns a compiler theorem into direct artifact-proof support.  The compiler-derived descriptor states what the IR body computes, the generated region equality checks what the selected WAT instructions are, and the generic semantic theorem connects the descriptor program to weakest-precondition execution.  The artifact proof still supplies and proves the mathematical loop invariant, so the path does not assume whole-compiler correctness or transport a source theorem.

## Descriptor package check

The first implementation added `ScalarTransition.guardedBackEdgeProgram_spec` in its own compiled ProofKit module.  The theorem accepts arbitrary scalar body, condition, and continuing descriptors, as well as arbitrary compact states, store, following program, and postcondition.  A focused module build and the generated `Project.ProofKit.LTGCheck` target accepted the theorem and both declarations advertised by the new provisional LTG entry.

The first real annotation-package attempt reached the generated Lean declarations but failed because `Project.ProofKit.GuardedBackEdge` was absent from the canonical proof-kit source and import inventory.  Adding the module to that inventory made the proof source available to the isolated task and covered it with the proof-kit source digest.  This failure concerned package authority rather than the semantic theorem or exact WAT equality, and the preserved diagnostic identifies the distinction.

The second annotation-package attempt used Demo 9's unchanged artifact digest `aa263bbfa89c333f9fab497f1a2c370f476afc3419015d17b368cb7c8a6086d5`.  Lean accepted an equality between nested loop instructions 16 through 37 and `guardedBackEdgeProgram` with scratch start 11, the compiler-derived wrapping-add body, the done condition, and an index-increment continuation.  A separate silent `leanexegen verify` run accepted the complete package, establishing exact artifact linkage before any proof-generation measurement.

The generated recipe names the exact step equality, compact step program, body evaluator equation, condition evaluator equation, and generic semantic theorem.  Its body transition updates the accumulator by wrapping addition, stages the result, clears the done flag, and records release readiness, while its condition tests the done local against zero.  The fixed-artifact reproof described below retrieved and applied every one of these declarations.

## Out-of-sample multiplication result

`OPA-004` generated Demo 10 from a prose request for a bounded wrapping product.  The valid branch uses `Array.foldl` with initial accumulator one and wrapping `UInt64` multiplication, while the invalid branch returns an empty array.  The compiler produced a new 1,979-byte artifact with SHA-256 digest `a981c7882a51a0660e6dd1e17956b958f7b2e25cbc30618d12458601ef2d4baa` and a scalar fold descriptor whose body operation is `mul` rather than Demo 9's `add`.

The fresh proving agent searched the structured LTG indexes before reading entry bodies and retained eight entries: length dispatch, capacity, fold prefix, fold structure, traversal input, guarded back edge, result construction, and allocation.  It rejected singleton-wrapper and fixed-index examples because their annotation kinds and control shape did not match the artifact.  The agent found `FixedArrayPairResult.input_preserved_by_alloc`, which the earlier Demo 9 agent had reproved before the allocation entry advertised it.

The continuing loop branch applied `FixedArrayTraversalInput.continuingProgram_spec` and `ScalarTransition.guardedBackEdgeProgram_spec`.  The generic guarded theorem accepted the generated multiplication-body evaluator, done-condition evaluator, and index-continuation evaluator without a multiplication-specific ProofKit lemma.  `ArrayFold.foldPrefix_succ` supplied the application-level invariant update, separating the fold mathematics from the compiler-motif theorem.

Lean accepted the exact artifact theorem, and a separate silent `leanexegen verify -s` run accepted the retained package.  Stage 5 took 1,596.295 seconds, including 1,539.659 seconds in Codex and 43.451 seconds in outer acceptance.  The proof contains 572 lines, 1,931 whitespace-delimited words, and 30,577 bytes.

The Demo 10 run was 375.929 seconds, or 19.1 percent, faster than the 1,972.223-second Demo 9 guarded-back-edge run.  Its proof has 17 fewer lines, 277 fewer whitespace-delimited words, and 571 fewer bytes.  The programs, specifications, and generated modules differ, so these figures describe the two accepted runs rather than a controlled timing comparison; cross-operation theorem use and independent acceptance provide the principal evidence.

The journal identifies two remaining interface costs.  Partial applications of the dependent traversal theorem repeatedly shifted tactic bullets until the agent supplied every semantic premise by name, even though the LTG guidance recommends that form.  A generated adapter or a tactic that creates one named continuation goal would enforce the stable interface more reliably than prose guidance.

Broad simplification exceeded its step limit while proving the fold-prefix successor and remaining-input measure.  Explicit rewriting, a named encoded-successor equality, and a `change` to the compact invariant closed those goals without a higher limit.  The accepted proof uses `func0Def` explicitly on 24 lines for selected entry and frame reductions, so the proposed local-irreducibility experiment can affect implicit unfolding while preserving these explicit reductions; it cannot remove their elaboration cost by itself.

## Generated traversal-adapter result

The annotation generator now emits three declarations for each checked continuing fold edge: `<region>_continuing_frame`, `<region>_continuing_item_valid`, and `<region>_continuing_spec`.  The theorem fixes the compiler-selected array, index, stop, and item locals, then exposes five semantic premises: the encoded-index equality, continuing inequality, represented input, logical index bound, and dependent continuation.  The generated proof applies `FixedArrayTraversalInput.continuingProgram_spec` with every structural premise named, so artifact proofs no longer reproduce its dependent application protocol.

A manual substitution in Demo 10 replaced thirteen lines in the accepted proof with six lines that apply the generated theorem and supply its five semantic premises.  Lean accepted the complete `ArtifactResult` target with a 565-line, 1,896-word, 30,173-byte proof, compared with 572 lines, 1,931 words, and 30,577 bytes before the substitution.  This check isolates the source-level substitution but does not measure fresh proof generation or prove that the shorter application changes elaboration time.

The fixed-artifact reproof retained the same formal specification, source, 1,979-byte WASM module, and artifact digest `a981c7882a51a0660e6dd1e17956b958f7b2e25cbc30618d12458601ef2d4baa`.  The fresh agent found `fixed-array-traversal-input` on its first structured LTG query, selected the generated adapter from the proof recipe, and applied `<region>_continuing_spec` at the remaining continuing edge.  Lean accepted the artifact theorem, and a separate `leanexegen verify -s` run accepted the retained package.

Stage 5 took 1,906.536 seconds, including 1,852.448 seconds in Codex and 43.049 seconds in outer acceptance.  The preceding fixed-artifact Demo 10 proof took 1,596.295 seconds, making this run 310.241 seconds, or 19.4 percent, slower.  The new proof contains 669 lines, 2,435 whitespace-delimited words, and 35,871 bytes, increases of 97 lines, 504 words, and 5,294 bytes.

The fresh proof used the adapter but defined its loop invariant and intermediate equalities in terms of the generated 21-value frame.  The resulting source refers to `<region>_continuing_frame` seventeen times and spells out the complete local vector at most uses, while the manual substitution allowed those values to infer from the existing compact fold frame.  The negative timing and size result therefore identifies an interface-use problem: generated adapters should cross one instruction boundary and leave the caller's semantic invariant intact.

The same journal found a separate proposition boundary at public entry.  A local `artifactPost` definition matched the generated result cases and formulas propositionally, but direct `change` did not establish definitional equality.  One `Wasm.wp.conseq` application proved the implication by simplification and let both length branches use the named postcondition, providing accepted `OPA-008` evidence without attributing the run's aggregate timing to that step.

The retained experiment package under `demos/demo-10/experiments/traversal-adapter.proof` contains the fixed artifact, generated declarations, fresh proof, journal, filtered LTG, recipes, and telemetry.  `demos/demo-10/experiments/manual-traversal-adapter.lean` preserves the smaller manual substitution.  Together they distinguish theorem applicability, concise expert use, and fresh-agent behavior rather than collapsing those questions into one measurement.

## Local-irreducibility screen

The first `OPA-006` screen added `attribute [local irreducible] ...func0Def` to the otherwise unchanged primary Demo 10 proof.  Lean reached the first `wp_fixed_array_length_le_dispatch_from` invocation and rejected its internal `change` after 4.3 seconds in the `Behavior` target.  The target still contained `func0Def.body`, `func0Def.results.length`, `func0Def.numParams`, and `func0Def.toLocals`, so the attribute hid every projection needed to establish the initial instruction and frame shape.

The second screen marked only the decoded body `func0` irreducible.  The same `change` failed after 5.2 seconds because `func0Def.body` reduces to the now-irreducible program name but cannot reduce further to `FixedArrayLengthDispatch.leProgram 7 8 validBranch invalidBranch`.  Both runs used the standard runner limits, stopped on a source diagnostic, and changed no theorem or artifact input.

These failures reject local irreducibility as an isolated proof setting under the current entry API.  A later test requires a checked package constructed before the opacity boundary: a compact public-entry theorem, an equality from `func0` to the named dispatch program, named valid and invalid branch programs, and checked subregion equalities used by each branch proof.  This design follows the VQ package technique because consumers use accessors and laws instead of unfolding the opaque decoded program.

The package must keep the branch proof usable without restating the complete WAT lists in theorem types.  Existing generated capacity, fold, traversal, guarded-step, and result equalities cover internal regions, but no current declaration composes them into named branch programs at the top-level dispatch.  The next PoC will add the smallest entry-to-branch composition needed for Demo 10, then judge whether the interface describes the common fixed-array wrapper motif before extending it.

The PoC added that composition for every checked length dispatch that begins at a function's first top-level instruction.  It names both complete branches, the generic dispatch program, and the following suffix, then proves the exact dispatch-region equality and complete function equality.  Demo 10's `leProgram` package and Demo 7's `eqProgram` package both compiled and passed independent package verification, including Demo 7's nonempty suffix.

The modified Demo 10 proof marks `func0` locally irreducible, changes the body-level entry goal to the named program, and rewrites it with `function_0_length_dispatch_0_function_eq`.  Every existing valid- and invalid-branch proof then checks without unfolding `func0`; only the named empty suffix required explicit reduction at the two terminal continuations.  The complete `ArtifactResult` target passed with no higher resource limits.

The proof grew from 572 to 578 lines, from 1,931 to 1,951 words, and from 30,577 to 31,087 bytes.  One warm build reported 8.2 seconds for `Behavior` and 2.1 seconds for `ArtifactResult`, compared with 9.0 and 2.3 seconds for the reducible proof under the same generated annotation package.  These single cached observations are inconclusive for timing, while the accepted theorem establishes that a compact accessor package can support a decoded-program opacity boundary that failed without it.

The generated annotation module grew from 11,597 to 24,930 bytes because it repeats the concrete valid and invalid branch instruction lists under stable names.  That duplication keeps the theorem types compact and branch programs reducible, but it increases package distribution and annotation checking.  A later representation can replace repeated branch bodies with checked opaque selectors plus sufficient subregion composition laws if the larger module becomes material.

## Compact loop-suffix theorem

The fresh fixed-artifact reproof received the complete entry-dispatch package, but the proving agent selected `wp_fixed_array_length_le_dispatch_from` and never used `function_0_length_dispatch_0_function_eq` or local irreducibility.  This supplies negative evidence for automatic retrieval of the opacity interface: the package remained available and checked, while the agent preferred the familiar direct tactic.  The run therefore does not measure the generated dispatch accessor's effect on fresh proof generation.

The agent reached a different elaboration boundary after allocation, input preservation, result-length storage, and fold setup had all succeeded.  Applying `Wasm.wp_loop_cons` with the complete result-placement suffix and public artifact continuation ended without a Lean diagnostic in four related builds; the runner explicitly reported the six-gibibyte child-memory ceiling for three of them.  Limiting pretty-print depth changed nothing, and inserting `Wasm.wp.conseq` with a compact loop-completion assertion inside `artifact_behavior` retained the same failure.

The accepted construction moved fold result placement, payload storage, singleton reconstruction, and final root transfer into the preceding `productSuffix_spec` theorem.  Its type starts at `productLoopFrame` with the logical index equal to the input size and ends at a small `productOutputPost` assertion.  Lean then checked the suffix declaration before elaborating `artifact_behavior`, restored ordinary local diagnostics at the loop boundary, and accepted the complete theorem after the remaining invariant and invalid-branch work.

Independent `leanexegen verify -s` accepted the preserved package over the unchanged 1,979-byte artifact with digest `a981c7882a51a0660e6dd1e17956b958f7b2e25cbc30618d12458601ef2d4baa`.  Stage 5 took 2,331.276 seconds, including 2,257.175 seconds in Codex and 55.754 seconds in outer acceptance, while the proof contains 687 lines, 2,347 words, and 35,160 bytes.  Relative to the retained 1,596.295-second, 572-line proof, this run was 46.0 percent slower and 115 lines longer, so `OPA-009` establishes a resource-boundary technique rather than a time or size improvement.

The journal also records one unchanged retry after the first silent failure.  That retry conflicts with the repository rule requiring proof or module division before another run without a diagnostic, and it produced no additional information.  The proof-agent prompt now states that timeout, memory-limit, or silent target failure requires a journal entry and a smaller theorem, module, or checked lemma before the next Lean check.

`FixedArrayFold.singletonResultProgram_spec` generalizes the accepted suffix declaration over arbitrary local roles, input frames, roots, values, and fold operations.  Its checked endpoint, `singletonResultPost`, records the return-local getter and singleton array representation without mentioning the enclosing invariant or public specification.  The theorem composes the existing accumulator-placement, payload-store, and root-transfer semantics rather than reproducing their instruction proofs.

The annotation consumer checks the complete trailing instruction sequence before exposing this theorem.  It accepts only the standard zero-index singleton payload address, the annotated result local as the stored value, one root local shared by the store and transfer, and a destination-to-return copy that ends the enclosing instruction list.  The generated equality connects this parameterized program to the exact decoded Demo 10 suffix.

Production annotation generation and separate package verification passed over the unchanged artifact and proof.  That package establishes exact linkage and theorem availability, while its retained behavioral proof does not use the new theorem.  The fresh reproof below measures selection, the remaining artifact-local adapters, proof structure, and Stage 5 time.

## Demo 10: generic singleton suffix use

The fresh proving agent began with category-index search and selected `compact-loop-suffix-boundary` together with the dispatch, capacity, allocation, fold, traversal, and guarded-back-edge entries.  It rejected map, filter, search, direct-call, and worked-example entries from their indexed annotation kinds and structural summaries.  The generated recipe supplied the exact decoded suffix equality and `FixedArrayFold.singletonResultProgram_spec`, so selection required no task-specific instruction.

The accepted `productSuffix_spec` changes the generated suffix to `FixedArrayFold.singletonResultProgram`, applies `Wasm.wp.conseq` to bridge its compact endpoint to the public postcondition, and discharges the instruction interval with `singletonResultProgram_spec`.  The local adapter still proves concrete frame validity and the public result implication, so it occupies 83 lines rather than eliminating the declaration.  Its semantic body contains one shared suffix-theorem application instead of separate applications for accumulator placement, payload storage, and final root transfer.

The run then reached `Wasm.wp_loop_cons` under the generated scalar frame and exhausted the one-million-heartbeat limit during invariant initialization and loop-step weak-head reduction.  The agent did not repeat the unchanged target.  It introduced the exact `productFoldFrame_eq`, after which both failures disappeared, and then built `productLoopBody_spec` around the generated traversal theorem, compiler-derived multiplication, condition, and index transitions, and `guardedBackEdgeProgram_spec`.

Lean accepted the complete artifact theorem, and a separate `leanexegen verify -s` run accepted the preserved package over the unchanged 1,979-byte artifact with digest `a981c7882a51a0660e6dd1e17956b958f7b2e25cbc30618d12458601ef2d4baa`.  Stage 5 took 2,998.613 seconds, including 2,875.208 seconds in Codex and 110.879 seconds in outer acceptance.  The proof contains 707 lines, 3,072 whitespace-delimited words, and 34,081 bytes.

The run is 667.337 seconds, or 28.6 percent, slower than the earlier artifact-local compact-suffix proof and 1,402.318 seconds, or 87.8 percent, slower than the retained primary proof.  Its line count is twenty lines above the compact-suffix proof, while its byte count is 1,079 bytes lower; identifier and word length do not constitute proof-complexity penalties.  The result establishes automatic retrieval, shared-theorem use, compiler-evidence composition, and independent acceptance, while supplying negative evidence for proof-generation time and line count.

`OPA-010` records the fold-body composition boundary.  The traversal-exit theorem, generated continuing theorem, scalar evaluator equations, and guarded-back-edge theorem already existed, but the agent had to compose them in a 155-line local helper before the enclosing loop rule became tractable.  The extracted theorem now parameterizes the scalar descriptors and compact states while leaving multiplication, `ArrayFold.foldPrefix`, invariant reconstruction, and measure decrease in caller callbacks.

`FixedArrayFoldBody.continuingGuardedProgram_spec` combines the active traversal guard and indexed load with `ScalarTransition.guardedBackEdgeProgram_spec`.  A new generated loaded-frame equality connects the checked dynamic loader to the scalar state expected by the compiler-derived body evaluator.  This split prevents the shared theorem from acquiring the 21-value Demo 10 invariant or any product-specific mathematics.

The production Demo 10 annotation package passed independent verification with the new equality and recipe over the unchanged artifact.  A manual substitution in the fresh singleton-suffix proof removed the artifact-local loaded-frame theorem and replaced the separate traversal and guarded-step applications with the shared theorem.  Lean accepted the complete `ArtifactResult` target, reducing the source from 707 to 704 lines and from 3,072 to 3,065 whitespace-delimited words.

This manual result establishes that the theorem type fits the observed proof boundary and reduces repeated semantic composition.  It does not supply proof-generation-time evidence or fresh-agent retrieval evidence.  The following fixed-artifact Demo 10 reproof and Demo 9 transfer screen supplied that evidence.

The fresh Demo 10 reproof supplied the missing selection and generation evidence.  The agent found `fixed-array-fold-body` on its second structured query, inspected its entry, and applied `continuingGuardedProgram_spec` to the exact concatenation of the generated traversal and guarded-step programs.  Independent verification accepted the package over the unchanged artifact digest.

Stage 5 completed in 1,913.092 seconds, 36.2 percent below the preceding 2,998.613-second singleton-suffix reproof and 19.8 percent above the 1,596.295-second primary proof.  The source fell from 707 to 650 lines and from 3,072 to 2,102 whitespace-delimited words relative to the preceding reproof.  The byte count rose from 34,081 to 36,253 because the proof names generated and shared declarations explicitly; identifier length does not count as proof complexity.

The journal records three avoidable iterations in the new theorem application.  Dependent inference postponed the item-validity and logical-index premises, shifting positional bullets into the loaded-frame and evaluator goals.  The LTG guidance now requires every structural and dependent premise by name and recommends direct rewriting with the generated continuing evaluator.

The Demo 9 transfer kept the exact wrapping-sum artifact and retrieved `fixed-array-fold-body` in its first structural query.  The accepted proof supplied every dependent premise by name and used the shared theorem with the generated wrapping-add body, false condition, continuing increment, loaded-frame equality, and exact WAT-region equalities.  Independent package verification accepted the unchanged 1,979-byte artifact and digest `aa263bbfa89c333f9fab497f1a2c370f476afc3419015d17b368cb7c8a6086d5`.

Stage 5 took 2,074.169 seconds, 5.2 percent more than the preceding guarded-back-edge screen and 0.4 percent less than the retained fold-structure proof.  The source has 588 lines, 2,484 whitespace-delimited words, and 29,973 bytes, compared with 589 lines, 2,208 words, and 31,148 bytes for the guarded-back-edge proof.  These measurements establish no time or uniform size improvement, while accepted retrieval across addition and multiplication supports the shared interface as a compiler motif.

The named-premise correction transferred: the Demo 9 theorem application had no dependent-premise bullet shift.  The journal exposed two remaining general instructions, namely fixing `module_`, `env`, `st`, and `frame` when callback inference generalizes them and naming all projections of a proof-local invariant frame before composing suffix theorems.  The promoted LTG entry now records those instructions and the mixed measurement rather than attributing a performance gain to the theorem.

## Fixed-artifact compiled-boundary result

The controlled reproof retained Demo 9's formal specification, source, 1,979-byte WASM module, and artifact digest.  Its first structured query selected `guarded-back-edge` with the fold, traversal, frame, dispatch, capacity, allocation, and result entries.  The agent inspected the entry, retained it because its annotation kind and recipe declarations matched the frozen artifact, and imported the checked module without searching outside the isolated task.

After the traversal theorem loaded `input[index]`, Lean's residual program was exactly the generated `guardedBackEdgeProgram 11`.  `guardedBackEdgeProgram_spec` accepted the compiler-generated body evaluator, condition evaluator, false control edge, successor prefix invariant, and strict remaining-input measure.  The proof never reduced the accumulator-update WAT instructions beneath the enclosing loop postcondition.

The continuing index assignment exposed a narrower elaboration boundary.  A broad reduction through generic `ScalarTransition.State.get` and `State.set?` exceeded the simplifier step limit, while `Stmt.eval_toState` followed by a finite `U64State` reduction checked the same assignment without a higher limit.  The compiler already constructs the continuing descriptor, so the annotation generator can emit its compact transition theorem beside the body and condition theorems.

| Field | Observation |
|---|---|
| Artifact | Demo 9, 1,979 bytes, digest `aa263bbf...a6086d5` |
| Generated WAT boundary | Nested loop instructions 16 through 37 |
| LTG retrieval | `guarded-back-edge` selected on the first structural query |
| Shared theorem | `ScalarTransition.guardedBackEdgeProgram_spec` |
| Compiler-derived evidence | Exact step equality plus body and condition evaluator theorems |
| Result | Artifact theorem accepted; independent package verification accepted |
| Stage 5 | 1,972.223 seconds; 1,872.127 seconds in Codex; 79.123 seconds in outer acceptance |
| Proof size | 589 lines; 2,208 whitespace-delimited words; 31,148 bytes |
| Compared with retained primary | 5.3 percent faster; 15.9 percent more lines |
| Compared with local compact boundary | 14.2 percent faster; 10.1 percent fewer lines |

The result supplies positive evidence for the compiled semantic boundary and a small timing improvement over the retained primary.  One run cannot separate the effect from agent and machine variation, and the larger proof prevents a proof-size improvement claim.  The package under `demos/demo-9/experiments/guarded-back-edge.proof` preserves the artifact, proof, journal, filtered LTG, recipes, generated equalities, and telemetry.

The journal also recorded two support defects outside the new boundary.  The agent reproved input preservation across the allocator even though `FixedArrayPairResult.input_preserved_by_alloc` already exists, and dependent premise inference for `FixedArrayTraversalInput.continuingProgram_spec` caused several shifted tactic-goal attempts before named arguments succeeded.  LTG should advertise the existing preservation theorem, while traversal guidance or a generated adapter should provide a stable named application form.

The journal survived a prover-context compaction and restored the exact last accepted boundary, diagnostic, intended edit, and expected residual goal.  This recovery avoided reconstructing the proof state from the 500-line candidate and provides direct evidence for frequent natural-prose journals.  The later research note should distinguish this recovery result from theorem effectiveness and proof-generation timing.

The generated `AnnotationMatches` module contains 148 lines, 936 words, and 9,180 bytes, with an 848-character maximum line in the explicit scalar transition theorems.  Those theorems quantify over 21 `UInt64` values, making inferred internal proposition aliases and a compact transition-specification package plausible later experiments.  The out-of-sample fold and generated continuing-transition theorem take precedence because the current package compiled and applied successfully.

The follow-up generator now emits `step_continuingTransition`, its checked `evalU64` theorem, and a typed `step_continuing_eval` theorem from the annotation-selected index local.  Demo 9's unchanged artifact accepted the generated theorem, added it to the fold recipe, and passed separate package verification.  This removes the exact generic-state simplification that failed during the measured run, while its effect on agent behavior and time remains unmeasured.

## Demo 9: continuing fold edge

The controlled run reproved Demo 9 against its unchanged 1,979-byte WebAssembly artifact with SHA-256 digest `aa263bbfa89c333f9fab497f1a2c370f476afc3419015d17b368cb7c8a6086d5`.  The generated program computes a wrapping `UInt64` sum over a bounded input array and returns a singleton array, or an empty array when the input exceeds the bound.  Earlier checked boundaries cover public entry, length dispatch, capacity calculation, allocation, result stores, fold setup, the indexed-load prefix, loop exit, result placement, and final root transfer.

The remaining continuing edge contains a staged accumulator update, a zero done flag, an index increment, and `Break 0`.  Applying a broad weakest-precondition simplifier directly reached the expected nested local-update term but exhausted the declaration's one-million-heartbeat limit because the large outer loop continuation remained in each reduction.  This failure identifies elaboration of the enclosing continuation as the immediate cost; it does not show a missing arithmetic lemma or a false invariant.

The proving agent introduced `foldUpdateProgram_spec`, a continuation-generic theorem for the exact post-load instruction tail.  Its endpoint is `foldUpdateFrame frame (accumulator + item) (index + 1)`, and its postcondition is an arbitrary `Q` applied to `Break 0` at that compact frame.  The theorem first projects `Locals.get` hypotheses to internal-list facts through `Frame.internal_getElem_of_get`, then checks the straight-line instruction semantics without carrying the outer invariant through each step.

| Field | Observation |
|---|---|
| Artifact | Demo 9, 1,979 bytes, digest `aa263bbf...a6086d5` |
| Failed boundary | Post-load fold update under the complete loop continuation |
| Failure | Heartbeat exhaustion during focused weakest-precondition simplification |
| Compact endpoint | `foldUpdateFrame frame (accumulator + item) (index + 1)` |
| Interface property | Arbitrary module, store, host environment, postcondition, and continuation |
| Required projections | Accumulator, item, and index from combined locals to internal locals |
| First result | The compact update theorem checks after using shared frame projections |
| Result | Artifact theorem accepted; independent package verification accepted |
| Stage 5 | 2,297.877 seconds monotonic; 2,251.334 seconds in Codex; 35.168 seconds in outer acceptance |
| Proof size | 655 lines; 2,472 whitespace-delimited words; 32,143 bytes |

The accepted proof applies `foldUpdateProgram_spec` after the checked input guard and load, then establishes the fold-prefix invariant and decreasing measure from the compact frame.  Two further artifact-local getter lemmas prevent simplification from opening the dynamic traversal frame when reading an overwritten index or the final root after stack reset.  The package under `demos/demo-9/experiments/compact-fold-boundary.proof` preserves the proof, journal, telemetry, compiler annotations, filtered LTG, and exact artifact.

The theorem currently fixes the emitted local indices and wrapping-add update sequence.  That form constitutes useful worked-example evidence, but one program does not justify promotion as a shared fold abstraction.  A second fold artifact with a different operation will test whether the reusable boundary is the staged control and index update, the accumulator operation, or a parameterized composition of both.

The complete run took 2,297.877 seconds, 10.3 percent longer than the retained 2,082.889-second fold-structure proof.  It took 25.2 percent less time than the 3,070.994-second capacity-and-frame screen and 33.0 percent less than the 3,431.870-second baseline.  The comparison establishes completion through the compact boundary, while the slower primary comparison and 28.9-percent line increase prevent a claim that opacity reduced total proof-generation time.

## Planned controlled experiments

The first experiment preserved Demo 9's source, specification, WebAssembly bytes, and public artifact theorem while comparing the accepted proof with earlier fixed-artifact runs.  Its UTC timestamps span 8,232.908 seconds, while the monotonic Stage 5 duration is 2,297.877 seconds; the 5,935.031-second difference remains separate from timing comparisons.  The accepted result supplies structural evidence for the boundary and negative evidence for a time or proof-size improvement over the retained proof.

The second experiment moved the guarded update theorem into a small ProofKit module and repeated the same fixed-artifact proof.  The generated exact interval equality connected the frozen WAT to the compiled theorem, and the agent used compiler-derived scalar transition equations to apply it.  Independent verification accepted the package in 1,972.223 seconds of Stage 5 work without changing the artifact bytes or assuming source-level compiler correctness.

The third experiment used Demo 10's multiplication fold with the same emitted traversal structure.  The accepted proof retrieved and applied the generic staged-control theorem, while the generated scalar evaluator equation supplied the operation-specific accumulator step.  This second consumer supports promotion of `guarded-back-edge` as a compiler-runtime motif without treating either fold's mathematical invariant as shared support.

The fourth experiment generated a complete continuing-edge adapter and tested it through a manual substitution and a fresh fixed-artifact reproof.  Both proofs passed, but the fresh agent expanded the generated frame through its invariant and produced a slower, larger proof.  The next adapter experiment will test an inferred internal proposition or a smaller frame-view interface that permits local values to infer from the caller's existing invariant.

The fifth experiment applied local irreducibility to the generated function definition and then to the decoded body alone.  Both standalone variants failed at the first length-dispatch `change`, before either branch proof, because the current entry API depends on definitional reduction of the decoded program.  The generated dispatch package then supplied the required accessors, and the modified proof passed with the decoded body irreducible.

The sixth experiment gave the complete suffix package and LTG guidance to a fresh fixed-artifact proving agent.  The agent selected the singleton-result theorem but retained the ordinary reducible entry-dispatch tactic, so automatic suffix selection succeeded while automatic use of the function-opacity equality remained absent.  The accepted and independently verified proof was slower and slightly longer than the earlier compact-suffix proof.

The seventh experiment extracted the recurring traversal-plus-guarded-back-edge composition from `productLoopBody_spec`.  Its shared interface accepts arbitrary scalar descriptors, compact states, postcondition callbacks, and exact compiler-generated traversal and scalar-transition evidence.  The manual and fresh Demo 10 screens passed, and the out-of-sample Demo 9 sum fold retrieved and applied the same theorem under independent package verification.

The eighth experiment generated exact parameter, local-length, operand-stack, and combined-getter theorems for each compiler-described continuing fold frame.  A manual Demo 9 substitution used these declarations with two shared result-frame getters, removed ten local projection theorems, and passed independent package verification.  The next fixed-artifact screen can measure whether an agent retrieves these accessors and avoids the representation detour without instructions tailored to Demo 9.

## Evidence rules

An accepted artifact theorem and independent package verification remain mandatory for every positive result.  A lower proof-generation time is useful evidence, but proof structure, the number of agent revisions, retrieval behavior, and applicability to a different artifact also determine whether a boundary belongs in shared LTG.  Increased heartbeat or memory limits do not establish an abstraction improvement.

The journal must record the last successful semantic boundary, the exact failed goal class, the attempted compact interface, and whether Lean checked the helper independently of the outer theorem.  It must also distinguish a theorem-body cost from a large theorem-type cost, since opacity addresses only the former.  These records will support a research note about checked semantic boundaries rather than a claim based on one favorable timing measurement.
