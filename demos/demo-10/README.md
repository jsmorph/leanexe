# Bounded wrapping-product artifact walkthrough

## Summary

This demo accepts an `Array UInt64`.  An input containing at most eight elements returns a singleton array whose element is the wrapping product of the input from left to right, starting with one.  A longer input returns an empty array.

The 1,979-byte WASM module has SHA-256 digest `a981c7882a51a0660e6dd1e17956b958f7b2e25cbc30618d12458601ef2d4baa`.  Its theorem proves the requested behavior directly from the decoded bytes under the pinned Talos semantics.  A separate `leanexegen verify -s` run accepted the retained proof package.

Demo 10 tests the guarded-back-edge support outside the wrapping-sum artifact that motivated it.  The compiler emitted a multiplication descriptor, and the fresh proving agent retrieved the same generic theorem through structured LTG.  The accepted proof applies the generated multiplication, exit-condition, and index-continuation evaluator equations without adding a multiplication-specific ProofKit theorem.

## Program and specification

The [generation request](request.txt) fixes the public behavior, maximum input length, wrapping multiplication, initial accumulator, and required traversal loop.  The [formal specification](spec.lean) defines the expected result, runtime precondition, and artifact property.  The [generated Lean program](program.lean) implements the valid branch with `Array.foldl`.

```lean
def compute (input : Array UInt64) : Array UInt64 :=
  if input.size ≤ 8 then
    #[input.foldl (fun product element => product * element) 1]
  else
    #[]
```

The [WASM module](program.wasm) is the exact executable covered by the theorem.  The [WAT rendering](program.wat) exposes its length dispatch, allocator branches, input-traversal loop, wrapping multiplication, and result stores.  The artifact theorem refers to the WASM bytes rather than the Lean source or compiler.

## Artifact proof

The [compiler annotations](program.annotations.json) describe the bounded-length dispatch, fixed branch capacities, and nested array-fold region.  The [generated annotation equalities](annotation-matches.lean) connect exact decoded WAT intervals to the fold setup, traversal prefix, descriptor-guided guarded back edge, and result placement.  The guarded-step package includes checked evaluator theorems for the multiplication body, done condition, and index increment.

The [proof recipe plan](proof-recipes.json) names the generated equalities and shared ProofKit declarations available for composition.  The [selected strategy notes](proof-strategies.md) and [program feature report](proof-task-features.json) supplied structured retrieval guidance without exposing a proof for this artifact.  The fresh agent selected the dispatch, capacity, fold-prefix, fold-structure, traversal, guarded-back-edge, result, and allocation entries.

The [behavioral proof](proof.lean) applies `FixedArrayPairResult.input_preserved_by_alloc` after result allocation, then carries `ArrayFold.foldPrefix` as the mathematical loop coordinate.  Its continuing branch applies `FixedArrayTraversalInput.continuingProgram_spec` and `ScalarTransition.guardedBackEdgeProgram_spec` with all three compiler-generated evaluator equalities.  Its exit branch uses the checked fold result, payload store, singleton representation, and final root-transfer theorems.

The [proof journal](proof-journal.md) records each retrieval decision, accepted semantic boundary, failed reduction, residual goal, and intended next edit.  It confirms that the newly advertised allocator input-preservation theorem was found, while partial dependent-premise applications again shifted traversal goals until every semantic premise was supplied by name.  Broad simplification also exceeded its step limit around the fold successor, after which explicit rewrites closed the successor invariant and termination measure.

## Measurement

The [proof telemetry](proof-telemetry.json) records 1,596.295 seconds from the start of Stage 5 to the first accepted proof, including 1,539.659 seconds in Codex and 43.451 seconds in outer acceptance.  The accepted proof contains 572 lines, 1,931 whitespace-delimited words, and 30,577 bytes.  The [timing comparison](proof-timings.json) records the corresponding Demo 9 guarded-back-edge measurement and size counts without treating the two different programs as a controlled timing pair.

Demo 10 completed Stage 5 375.929 seconds, or 19.1 percent, faster than the Demo 9 guarded-back-edge run.  Its proof contains 17 fewer lines, 277 fewer whitespace-delimited words, and 571 fewer bytes.  Agent and machine variation prevent assigning those differences to multiplication or to a single support change, while the accepted theorem establishes cross-operation applicability.

The [stage reports](stage-reports.json) record the accepted formal specification, generated source, and artifact-proof source identities.  Both specification and source passed on their first candidates.  The artifact proof passed after fourteen recorded import-check iterations and one final definitional result-store normalization.

## Traversal-adapter experiment

The annotation generator later added a complete theorem for the checked continuing traversal prefix.  A manual substitution in the retained proof replaced the direct dependent application of `FixedArrayTraversalInput.continuingProgram_spec` with the generated theorem.  The [manual adapter proof](experiments/manual-traversal-adapter.lean) passed the complete `ArtifactResult` build and decreased the source from 572 to 565 lines, from 1,931 to 1,896 words, and from 30,577 to 30,173 bytes.

A fresh fixed-artifact reproof found and applied the same generated theorem through structured LTG and the annotation recipe.  The independently verified [adapter experiment package](experiments/traversal-adapter.proof/) preserves its proof, journal, generated declarations, telemetry, and fixed WASM artifact.  The artifact digest and all program inputs remain unchanged.

The fresh run took 1,906.536 seconds in Stage 5, which is 310.241 seconds, or 19.4 percent, slower than the primary run.  Its proof grew to 669 lines, 2,435 words, and 35,871 bytes because the agent rebuilt much of its invariant around the generated 21-value frame, referring to that frame seventeen times.  The manual result shows a compact use of the theorem, while the fresh result directs LTG guidance to preserve the caller's semantic frame and let generated local values infer at the single traversal boundary.

The [local-irreducibility screen](experiments/irreducibility-screen.md) tested the VQ technique against the primary proof without changing its artifact or theorem.  Marking either the complete function definition or its decoded body irreducible blocked the first length-dispatch `change` within 5.2 seconds of target work.  The result records a required predecessor: generated entry, dispatch, and named-branch accessors must expose the proof interface before any decoded-program opacity boundary can work.

The follow-up [entry-dispatch package](experiments/entry-dispatch.proof/) names the exact valid branch, invalid branch, dispatch program, and trailing program, then proves that their composition equals the decoded function.  Independent verification accepted the package over the unchanged artifact, and the [irreducible dispatch proof](experiments/irreducible-dispatch-proof.lean) passed `ArtifactResult` after rewriting through that equality.  This proof keeps `func0` irreducible while leaving both named branches available to the existing capacity, allocator, fold, and result theorems.

The modified proof contains 578 lines, 1,951 words, and 31,087 bytes, six lines and 510 bytes more than the primary proof.  One warm build took 8.2 seconds for `Behavior` and 2.1 seconds for `ArtifactResult`, compared with 9.0 and 2.3 seconds for a reducible build in a copied workspace.  These single acceptance measurements are descriptive, while successful checking establishes that a compact generated accessor can make the previously rejected opacity boundary usable.

## Compact suffix-boundary experiment

A fresh fixed-artifact reproof received the entry-dispatch package but selected the ordinary length-dispatch tactic.  It did not apply the generated function equality or mark the decoded function irreducible.  This run therefore leaves automatic use of the entry-opacity interface unestablished.

The proof reached the six-gibibyte memory ceiling while applying the loop rule under the complete result suffix and public continuation.  A compact consequence inside the public theorem retained the failure, while moving result placement, payload storage, singleton reconstruction, and root transfer into a preceding `productSuffix_spec` theorem restored ordinary diagnostics.  The agent then completed both length branches and the exact artifact theorem.

The independently verified [compact suffix package](experiments/compact-suffix-boundary.proof/) preserves the unchanged artifact, generated package, proof, journal, and telemetry.  Stage 5 took 2,331.276 seconds, and the proof contains 687 lines, 2,347 words, and 35,160 bytes.  The run is 46.0 percent slower and 115 lines longer than the retained proof, but it establishes that a separate compact theorem can turn a silent elaboration failure into a checkable proof boundary.

The follow-up [singleton-result suffix package](experiments/singleton-result-suffix.proof/) adds a generic `FixedArrayFold.singletonResultProgram_spec` theorem and a generated exact equality for the complete emitted suffix.  The theorem parameterizes all five local roles and the fold value, while its endpoint records the returned root and represented singleton array.  Production annotation generation and independent package verification accepted this interface over the same artifact.

The [fresh singleton-result reproof](experiments/singleton-result-suffix-reproof.proof/) retrieved the structured LTG entry and used the shared theorem inside a local adapter to the public postcondition.  Independent verification accepted the complete artifact theorem over the unchanged WASM digest.  This supplies automatic-selection and structural-use evidence, while the timing and line measurements are adverse.

Stage 5 took 2,998.613 seconds, including 2,875.208 seconds in Codex and 110.879 seconds in outer acceptance.  The accepted proof contains 707 lines, 3,072 whitespace-delimited words, and 34,081 bytes.  It is 28.6 percent slower and twenty lines longer than the earlier compact-suffix proof, although its semantic suffix body applies one shared theorem instead of composing three lower-level instruction theorems.

The journal records a second useful boundary.  The enclosing loop reached the one-million-heartbeat limit until the proof introduced an exact generated-frame equality, then required a continuation-generic local theorem to compose the traversal, compiler-derived scalar transitions, guarded back edge, invariant, and measure.  This composition is the next candidate for shared ProofKit and annotation support, with Demo 9 available as an out-of-sample sum-fold consumer.

## Shared fold-body composition experiment

`FixedArrayFoldBody.continuingGuardedProgram_spec` now composes the active traversal guard and indexed load with an arbitrary compiler-described scalar body, condition, continuation, and guarded back edge.  Its callbacks leave the fold invariant, operation, successor equation, measure, and public postcondition to the artifact proof.  The annotation generator supplies `function_0_array_fold_0_continuing_loaded_frame_eq`, which identifies the checked loader result with the generated scalar frame consumed by the evaluator theorems.

The [capability package](experiments/fold-body-composition.proof/) contains the exact generated equality and recipe declaration over the unchanged 1,979-byte artifact.  A separate `leanexegen verify -s` run accepted that package.  Its retained behavioral proof predates the new theorem, so the package establishes exact linkage and theorem availability rather than use by a proving agent.

The [manual fold-body adapter](experiments/manual-fold-body-adapter.lean) replaces the local loaded-frame theorem and the separate traversal and guarded-back-edge applications in the fresh singleton-suffix proof.  The complete `ArtifactResult` target passed, and the source changed from 707 lines, 3,072 words, and 34,081 bytes to 704 lines, 3,065 words, and 34,043 bytes.  This small structural reduction establishes that the shared interface fits the artifact proof; a fresh fixed-artifact reproof must test retrieval, automatic use, and proof-generation time.

The [fresh fold-body reproof](experiments/fold-body-reproof.proof/) retrieved the new LTG entry on its second structural query and applied `continuingGuardedProgram_spec` at the strict-index loop edge.  Its callbacks prove the wrapping-product prefix successor, reconstruct the invariant at `index + 1`, and establish the smaller remaining-input measure, while the shared theorem consumes the generated loaded-frame, multiplication, condition, and increment equations.  Independent verification accepted the complete package over the unchanged artifact digest.

Stage 5 took 1,913.092 seconds, including 1,778.739 seconds in Codex and 97.743 seconds in outer acceptance.  This is 1,085.521 seconds, or 36.2 percent, below the preceding 2,998.613-second singleton-suffix reproof, while the accepted source fell from 707 to 650 lines and from 3,072 to 2,102 whitespace-delimited words.  It remains 316.797 seconds, or 19.8 percent, slower than the 1,596.295-second primary Demo 10 proof and contains 78 more lines, so the result supports the shared composition without establishing a new primary configuration.

The journal records twelve accepted import-check edits and three iterations caused by dependent premise inference in the new theorem application.  Naming `hItem`, `hInput`, and `hIndex` stabilized that application; the LTG entry now directs the prover to name every structural and dependent premise from the start.  The journal also recommends direct rewriting with the generated increment evaluator and local unfolding of the generated continuing frame, which will be tested on Demo 9.

## Generated frame-accessor capability

The [frame-accessor package](experiments/frame-accessors.proof/) regenerates the annotations and proof recipe for the unchanged Demo 10 artifact.  Its annotation module proves the continuing frame's parameter list, internal-local length, empty operand stack, and getter at each of the 21 combined parameter-and-local indices.  The recipe also names the shared result-frame getter and preservation theorems used by the Demo 9 substitution.

Independent `leanexegen verify -s` accepted the retained behavioral proof and exact artifact theorem with these declarations present.  The proof predates the accessors and therefore establishes annotation generation, Lean checking, recipe publication, and package compatibility rather than agent use.  Demo 9 supplies the separate accepted manual proof that uses the same generated interface and removes local projection declarations.

## Fresh frame-accessor reproof

The [fresh frame-accessor reproof](experiments/frame-accessor-reproof.proof/) held the specification, source, 1,979-byte WASM artifact, and digest fixed.  The accepted proof used the generated continuing-frame value-stack and index getters and both shared result-frame getter theorems.  Independent `leanexegen verify -s` accepted the preserved package.

The agent did not retrieve `annotated-fold-frame-accessors` by name, although the task contained that entry, the selected strategy notes described its use, and the recipe listed every generated accessor.  After the completed fold exposed frame-projection goals, the agent introduced local parameter-length, local-length, accumulator, and root facts by reduction and discharged several traversal premises with `rfl`.  The journal therefore identifies a retrieval checkpoint defect rather than missing annotation or ProofKit support.

Stage 5 took 2,099.237 seconds, including 2,031.417 seconds in Codex and 50.156 seconds in outer acceptance.  This was 186.146 seconds, or 9.7 percent, slower than the preceding fold-body reproof and 502.942 seconds, or 31.5 percent, slower than the primary proof.  The source decreased from 650 to 600 lines and from 36,253 to 30,568 bytes relative to the fold-body reproof, while its whitespace-delimited word count increased from 2,102 to 2,371.

The telemetry's UTC timestamps span 5,546.712 seconds, exceeding the monotonic Stage 5 measurement by 3,447.475 seconds.  Timing comparisons use the monotonic metric and preserve both timestamp forms in the package.  The proof prompt now treats each new residual goal class as another LTG retrieval checkpoint and requires an accessor search before proving a frame projection by reduction or a new local fact.

## Fold-completion adapter experiment

The [fold-completion package](experiments/fold-completion.proof/) checks the generated `function_0_array_fold_0_singleton_result_spec` theorem against the unchanged wrapping-product artifact.  The [manual proof](experiments/manual-fold-completion.lean) applies that theorem directly to the public valid-branch postcondition, replacing its proof-local result-frame facts and postcondition consequence.  The product-prefix invariant, heap-address argument, and represented singleton result remain in the artifact proof.

Independent `leanexegen verify -s` accepted the complete package and exact artifact digest.  The proof decreased from 600 to 553 lines, from 2,371 to 2,162 whitespace-delimited words, and from 30,568 to 28,254 bytes.  Demo 9 and Demo 11 apply the same operation-independent interface to wrapping addition and bitwise XOR.

This manual substitution provides no proof-generation-time measurement.  The package omits the predecessor proof's telemetry because those timings belong to a different source.  A fresh fixed-artifact reproof will measure structured retrieval and proof construction separately.

## Fold-completion and frame-projection transfer

The [fresh transfer package](experiments/fold-completion-projection-reproof.proof/) received the generic capacity and allocator frame projections, role-labelled continuing-frame recipe, fold-completion adapter, and structured LTG.  The agent selected `capacityFrame_internal_get_capacity` and `allocFrame_get_root` at its first allocation-boundary search and used both in the accepted invalid and valid branches.  It also selected and applied the generated singleton-result adapter, shared fold-body theorem, exact loaded-frame equality, and compiler-generated multiplication evaluator equations.

Stage 5 took 1,979.854 seconds, including 1,912.675 seconds in Codex and 59.059 seconds in outer acceptance.  The run was 119.383 seconds, or 5.7 percent, faster than the 2,099.237-second frame-accessor screen, but 66.762 seconds, or 3.5 percent, slower than the 1,913.092-second fold-body screen.  It remained 383.559 seconds, or 24.0 percent, slower than the 1,596.295-second primary proof, so the transfer supplies no new best timing result.

The accepted source contains 684 lines, 2,875 whitespace-delimited words, and 36,126 bytes.  It is 84 lines and 504 words larger than the frame-accessor proof and 131 lines and 713 words larger than the manual fold-completion proof.  The journal records fourteen successful import-and-build cycles, including two parser-name conflicts, one positional dependent-premise failure before the agent followed the named-premise guidance, and one unrestricted simplifier step-limit failure.

The experiment establishes that the new projections and completion adapter transfer from wrapping addition to wrapping multiplication.  The role-labelled recipe names `releaseReadyLocal` and its exact getter, although this proof represented the complete generated frame and did not invoke that getter directly.  Separate `leanexegen verify -s` accepted the package over the unchanged digest `a981c7882a51a0660e6dd1e17956b958f7b2e25cbc30618d12458601ef2d4baa`.

## Execution

The empty input checks the multiplicative identity, the second sample checks the traversal loop, and the third checks the oversized branch.  Direct execution of the proved artifact produced these results.  Each result agrees with the formal specification.

```text
Input: []
Output: [1]
Input: [2, 3, 4]
Output: [24]
Input: [1, 2, 3, 4, 5, 6, 7, 8, 9]
Output: []
```

## Retained files

The root files provide readable views of each generation and proof stage.  The [verification package](program.proof/) preserves the embedded artifact, generated proof modules, filtered LTG snapshot, tool pins, manifest, journal, and telemetry accepted by the independent verifier.  The table identifies every retained root file and the package directory.

| File | Contents |
|---|---|
| [Generation request](request.txt) | The bounded wrapping-product behavior supplied to leanexegen. |
| [Formal specification](spec.lean) | The expected result, runtime precondition, and artifact property. |
| [Lean program](program.lean) | The generated source compiled by LeanExe. |
| [WASM module](program.wasm) | The exact executable artifact covered by the theorem. |
| [WAT rendering](program.wat) | The textual instruction representation of the artifact. |
| [Behavioral proof](proof.lean) | The accepted direct proof of the artifact behavior. |
| [Compiler annotations](program.annotations.json) | The compiler-emitted structural descriptions consumed by the matcher. |
| [Annotation equalities](annotation-matches.lean) | The generated exact-region and scalar-evaluator theorems. |
| [Proof recipe plan](proof-recipes.json) | The checked declarations and composition suggestions selected from annotations. |
| [Selected strategy notes](proof-strategies.md) | The structured proof guidance supplied to the agent. |
| [Program feature report](proof-task-features.json) | The artifact, annotation, and LTG retrieval features. |
| [Proof journal](proof-journal.md) | The agent's searches, failed checks, decisions, and residual goals. |
| [Proof telemetry](proof-telemetry.json) | The Stage 5 timing intervals and accepted proof digest. |
| [Timing comparison](proof-timings.json) | The Demo 10 measurement and descriptive Demo 9 comparison. |
| [Stage reports](stage-reports.json) | The accepted specification, source, and artifact-proof reports. |
| [Verification package](program.proof/) | The self-contained package accepted by `leanexegen verify -s`. |
| [Manual traversal-adapter proof](experiments/manual-traversal-adapter.lean) | A checked substitution that shortens the primary proof's dependent traversal application. |
| [Fresh traversal-adapter package](experiments/traversal-adapter.proof/) | The independently verified fixed-artifact reproof, journal, LTG snapshot, and telemetry. |
| [Local-irreducibility screen](experiments/irreducibility-screen.md) | The two focused failure diagnostics and the required compact-accessor boundary. |
| [Entry-dispatch package](experiments/entry-dispatch.proof/) | The independently verified named branch, dispatch, suffix, and function equalities. |
| [Irreducible dispatch proof](experiments/irreducible-dispatch-proof.lean) | The checked primary proof with a local decoded-body opacity boundary. |
| [Compact suffix package](experiments/compact-suffix-boundary.proof/) | The independently verified reproof whose separate suffix theorem removed the loop-rule memory failure. |
| [Singleton-result suffix package](experiments/singleton-result-suffix.proof/) | The independently verified generic suffix theorem and exact decoded-region equality. |
| [Fresh singleton-result reproof](experiments/singleton-result-suffix-reproof.proof/) | The independently verified fixed-artifact run that selected the generic suffix theorem and exposed the next fold-body composition boundary. |
| [Fold-body capability package](experiments/fold-body-composition.proof/) | The independently verified generated loaded-frame equality, shared-theorem recipe, and unchanged artifact. |
| [Manual fold-body adapter](experiments/manual-fold-body-adapter.lean) | The checked singleton-suffix proof modified to use the shared traversal and guarded-step composition theorem. |
| [Fresh fold-body reproof](experiments/fold-body-reproof.proof/) | The independently verified fixed-artifact run that retrieved and used the shared fold-body theorem. |
| [Generated frame-accessor capability](experiments/frame-accessors.proof/) | The independently verified current annotation and recipe package containing exact accessors for all 21 continuing-frame slots. |
| [Fresh frame-accessor reproof](experiments/frame-accessor-reproof.proof/) | The independently verified fixed-artifact proof that used part of the accessor family and exposed a residual-goal retrieval defect. |
| [Fold-completion package](experiments/fold-completion.proof/) | The independently verified manual proof using the generated exact singleton-result adapter. |
| [Fresh fold-completion and projection transfer](experiments/fold-completion-projection-reproof.proof/) | The independently verified proof that retrieved and used the new capacity, allocator-root, fold-body, and completion interfaces. |
| [Manual fold-completion proof](experiments/manual-fold-completion.lean) | The readable behavioral proof retained by the fold-completion package. |
