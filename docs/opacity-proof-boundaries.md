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
| `OPA-006` | Local irreducibility | Decoded function after public-entry conversion | Proposed.  The experiment must retain the explicit reductions used by length dispatch and frame facts while preventing unification from reopening the complete function. |
| `OPA-007` | Named compact endpoint equality | Generated traversal program, frame, item-validity proof, and continuation theorem | Accepted on Demo 10 in both a manual substitution and a fresh fixed-artifact reproof.  The manual substitution shortened the existing proof, while the fresh proof expanded the generated frame throughout its invariant and was slower and larger. |
| `OPA-008` | Named proposition bridged by consequence | Public artifact postcondition after fixed-store entry conversion | Accepted in the fresh Demo 10 reproof.  Direct `change` failed even when the named definition repeated the generated expressions, while `Wasm.wp.conseq` established the implication and kept the compact name through both length branches. |

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

The fifth experiment will apply local irreducibility to the generated function definition after public-entry conversion.  The test will record whether routine unification stops reopening the decoded function while explicit `simp [func0Def]` calls still discharge the few frame-shape obligations that require reduction.  A silent timeout, recursion-depth failure, or slower accepted proof will reject this setting for automatic use while preserving the result as evidence.

## Evidence rules

An accepted artifact theorem and independent package verification remain mandatory for every positive result.  A lower proof-generation time is useful evidence, but proof structure, the number of agent revisions, retrieval behavior, and applicability to a different artifact also determine whether a boundary belongs in shared LTG.  Increased heartbeat or memory limits do not establish an abstraction improvement.

The journal must record the last successful semantic boundary, the exact failed goal class, the attempted compact interface, and whether Lean checked the helper independently of the outer theorem.  It must also distinguish a theorem-body cost from a large theorem-type cost, since opacity addresses only the former.  These records will support a research note about checked semantic boundaries rather than a claim based on one favorable timing measurement.
