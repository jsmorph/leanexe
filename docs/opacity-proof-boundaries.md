# Opacity and elaboration boundaries in artifact proofs

This file records experiments on reducing Lean elaboration cost in direct WebAssembly proofs.  The immediate source is [Opacity Boundaries for Large Lean Proofs](../../vq/docs/notes/research/lean-opacity-practical.md), which distinguishes checked opacity from compact interfaces and reports cases where generic specification packages removed expensive concrete comparisons.  Each Leanexe experiment records the fixed artifact, the expensive term, the proposed boundary, and the observed result so that a later research note can separate measured results from design hypotheses.

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

The third experiment will use a different fold operation and the same emitted traversal structure.  It will test a parameterized operation theorem or a separation between a generic staged-control theorem and an operation-specific accumulator lemma.  Promotion into automatically selected LTG guidance will require successful retrieval and use beyond Demo 9; a narrow theorem may remain in the catalog as a worked example when its proof-engineering lesson remains distinct.

The fourth experiment will apply local irreducibility to the generated function definition after public-entry conversion.  The test will record whether routine unification stops reopening the decoded function while explicit `simp [func0Def]` calls still discharge the few frame-shape obligations that require reduction.  A silent timeout, recursion-depth failure, or slower accepted proof will reject this setting for automatic use while preserving the result as evidence.

## Evidence rules

An accepted artifact theorem and independent package verification remain mandatory for every positive result.  A lower proof-generation time is useful evidence, but proof structure, the number of agent revisions, retrieval behavior, and applicability to a different artifact also determine whether a boundary belongs in shared LTG.  Increased heartbeat or memory limits do not establish an abstraction improvement.

The journal must record the last successful semantic boundary, the exact failed goal class, the attempted compact interface, and whether Lean checked the helper independently of the outer theorem.  It must also distinguish a theorem-body cost from a large theorem-type cost, since opacity addresses only the former.  These records will support a research note about checked semantic boundaries rather than a claim based on one favorable timing measurement.
