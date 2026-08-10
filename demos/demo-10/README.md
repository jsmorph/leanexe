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
