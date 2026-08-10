# Opacity and elaboration boundaries in artifact proofs

This file records experiments on reducing Lean elaboration cost in direct WebAssembly proofs.  The immediate source is [Opacity Boundaries for Large Lean Proofs](../../vq/docs/notes/research/lean-opacity-practical.md), which distinguishes checked opacity from compact interfaces and reports cases where generic specification packages removed expensive concrete comparisons.  Each Leanexe experiment records the fixed artifact, the expensive term, the proposed boundary, and the observed result so that a later research note can separate measured results from design hypotheses.

## Technique map

An opaque theorem helps only when its type omits the expanded term that caused the cost.  A theorem whose body is opaque but whose statement repeats a large decoded program, continuation, or concrete local frame still makes every consumer elaborate that expression.  Leanexe therefore needs small semantic endpoints: a named instruction region, a compact post-state description, and an arbitrary continuation or postcondition.

Module boundaries can make those endpoints reusable across artifact proofs.  A shared ProofKit module checks instruction semantics once, while a generated annotation module proves that a decoded artifact interval equals the shared program.  The artifact proof then composes the generated equality with the compiled semantic theorem, leaving program-specific invariants and specification facts outside the expensive instruction reduction.

Inferred proposition types may avoid a second elaboration of a large weakest-precondition expression.  Generated accessors and local `have` bindings can carry the checked proposition without restating its full type, provided that the final public theorem remains explicit and compact.  Local irreducibility may also prevent accidental reduction of a decoded function after entry decomposition, but an experiment must establish that it preserves the explicit reductions required for dispatch and local-frame facts.

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

The second experiment will move any justified update theorem into a small ProofKit module and repeat the same fixed-artifact proof.  This tests whether a compiled theorem boundary reduces downstream elaboration, rather than testing only whether a local helper changes proof organization.  The package will undergo independent verification, and the retained proof will continue to depend on the artifact bytes rather than a source-level compiler-correctness assumption.

The third experiment will use a different fold operation and the same emitted traversal structure.  It will test a parameterized operation theorem or a separation between a generic staged-control theorem and an operation-specific accumulator lemma.  Promotion into automatically selected LTG guidance will require successful retrieval and use beyond Demo 9; a narrow theorem may remain in the catalog as a worked example when its proof-engineering lesson remains distinct.

The fourth experiment will apply local irreducibility to the generated function definition after public-entry conversion.  The test will record whether routine unification stops reopening the decoded function while explicit `simp [func0Def]` calls still discharge the few frame-shape obligations that require reduction.  A silent timeout, recursion-depth failure, or slower accepted proof will reject this setting for automatic use while preserving the result as evidence.

## Evidence rules

An accepted artifact theorem and independent package verification remain mandatory for every positive result.  A lower proof-generation time is useful evidence, but proof structure, the number of agent revisions, retrieval behavior, and applicability to a different artifact also determine whether a boundary belongs in shared LTG.  Increased heartbeat or memory limits do not establish an abstraction improvement.

The journal must record the last successful semantic boundary, the exact failed goal class, the attempted compact interface, and whether Lean checked the helper independently of the outer theorem.  It must also distinguish a theorem-body cost from a large theorem-type cost, since opacity addresses only the former.  These records will support a research note about checked semantic boundaries rather than a claim based on one favorable timing measurement.
