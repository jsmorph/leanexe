# Bounded wrapping-sum artifact walkthrough

## Summary

This demo accepts an `Array UInt64`.  An input containing at most eight elements returns a singleton array whose element is the wrapping sum of the input.  A longer input returns an empty array.

The 1,979-byte WASM module has SHA-256 digest `aa263bbfa89c333f9fab497f1a2c370f476afc3419015d17b368cb7c8a6086d5`.  Its valid branch allocates a singleton result and traverses the input with an emitted loop, while its invalid branch allocates an empty result.  Independent `leanexegen verify -s` accepted the complete package and exact artifact theorem.

The retained fold-structure proof completed Stage 5 in 2,082.889 seconds and contained 508 lines.  It reduced measured time by 34.7 percent from the preceding annotation run and by 39.3 percent from the baseline.  The proof added 92 lines relative to the preceding run because it states two missing capacity-prefix lemmas locally and applies the shared setup, traversal, result-placement, and result-store boundaries explicitly.

## Program and specification

The [generation request](request.txt) fixes the public behavior, the maximum input length, and wrapping `UInt64` addition.  The [formal specification](spec.lean) defines the expected array and the branch-sensitive heap reserve required by the artifact theorem.  The [generated Lean program](program.lean) expresses the valid result with `Array.foldl`.

```lean
def compute (input : Array UInt64) : Array UInt64 :=
  if input.size ≤ 8 then
    #[input.foldl (fun sum element => sum + element) 0]
  else
    #[]
```

The [WASM module](program.wasm) is the executable covered by the theorem.  The [WAT rendering](program.wat) exposes the emitted length test, two fixed-array allocator paths, indexed input loads, wrapping accumulator update, and result stores.  The theorem refers to the exact module bytes rather than the Lean source or compiler.

## Artifact proof

The [compiler annotations](program.annotations.json) identify the bounded array-length dispatch and the nested array-fold region.  The [annotation equality](annotation-matches.lean) names the decoded fold interval at instructions 39 through 65 of the valid branch, its setup interval through instruction 62, the 16-instruction continuing guard-and-load prefix, and the accumulator-to-result transfer at instructions 63 through 65.  It also identifies the complete constant-capacity prefix at the start of each length branch.  Lean proves all six equalities by reduction, while the consumer checks the reported branch arithmetic, accumulator, item, index, effective-stop, staging, scratch, guard, element-address load, back-edge, and result-local roles against the decoded artifact.

The [proof recipe plan](proof-recipes.json) names `FixedArrayLengthDispatch.leProgram_spec`, both capacity equalities, all four fold-program equalities, `FixedArrayCapacity.constantProgram_spec`, `FixedArrayFold.forwardSetupProgram_spec`, both traversal-guard edge theorems, `FixedArrayFold.resultProgram_spec`, the frame-projection declarations, and the generic fold-prefix declarations.  The [selected strategy notes](proof-strategies.md) and [program feature report](proof-task-features.json) provide the structured LTG catalog, allocator guidance, array-framing guidance, and fold invariant.  The retained measured proof predates the capacity and exit declarations; it retrieved the earlier entries from its archived task-specific LTG view and used each of the three fold subregion theorems.

The [behavioral proof](proof.lean) uses `ArrayFold.foldPrefix` as the loop-carried mathematical coordinate.  It applies the checked fold-setup theorem before the invariant, the traversal theorem in the continuing case, `foldPrefix_succ` at the back edge, and the checked result-placement theorem after exit.  The proof also applies the shifted allocator theorem, length-store theorem, payload-store theorem, and final array-representation theorems to the exact decoded program.

The [proof journal](proof-journal.md) records the successful path and each rejected intermediate reduction.  Structured retrieval selected the generic dispatch, fold, traversal, result, allocation, and memory entries while excluding artifact-specific worked examples.  Its capacity-prefix and local-projection gaps led to `FixedArrayCapacity.constantProgram_spec` and the two `Frame` projection theorems, which the current package catalogs without changing the measured proof or artifact.

The [proof telemetry](proof-telemetry.json), [timing comparison](proof-timings.json), and [stage reports](stage-reports.json) preserve time intervals and source identities.  The retained proof has 508 lines, 2,155 whitespace-delimited words, and 24,327 bytes, compared with 416 lines, 1,848 words, and 17,797 bytes in the preceding annotation run.  Its 34.7-percent time reduction accompanies a 22.1-percent line increase, so the result supports faster proof generation and better shared-boundary use while recording a proof-size cost for the next LTG iteration.

## Capacity and frame comparison

The [current accepted comparison package](experiments/capacity-frame-current.proof/) holds the specification, source, and WASM fixed while adding exact capacity-prefix equalities, `FixedArrayCapacity.constantProgram_spec`, and the structured LTG.  Independent verification accepted its artifact theorem under the current proof-kit identity; the [original generation package](experiments/capacity-frame.proof/) preserves the proof kit supplied during generation.  Its monotonic Stage 5 measurement was 3,070.994 seconds, 47.4 percent slower than the retained fold-structure proof, while remaining 3.7 percent faster than the earlier fold-annotation proof and 10.5 percent faster than the baseline.

The comparison proof contains 642 lines, 2,524 words, and 30,858 bytes.  It uses the shared capacity theorem in both length branches and reaches the checked setup, traversal, result-placement, allocator, and result-store boundaries, but it adds local theorems for the traversal exit edge, the accumulator/index update, and two getters from the updated frame.  The exit edge and final root transfer have since become checked ProofKit theorems, and traversal guidance now names the shared combined-to-internal frame projection; the accumulator/index update remains a candidate compiler motif rather than a promoted general theorem.

The telemetry's UTC timestamps span 12,764.900 seconds, while its monotonic Stage 5 measurement records 3,070.994 seconds.  The 9,693.906-second difference occurred outside the monotonic interval, and the accessible system journal did not identify its cause.  Timing comparisons therefore use the telemetry's monotonic total, while `proof-timings.json` preserves both measurements.

## Compact fold-boundary comparison

The [compact-boundary package](experiments/compact-fold-boundary.proof/) tests the shared traversal-exit and final-transfer theorems together with an artifact-local, continuation-generic theorem for the post-load accumulator and index update.  Direct simplification of that update under the complete loop continuation exhausted one million heartbeats, while the compact theorem checked the instruction tail against a named frame and let the outer proof establish its invariant separately.  Independent package verification accepted the exact artifact theorem.

Stage 5 took 2,297.877 seconds, including 2,251.334 seconds in Codex and 35.168 seconds in outer acceptance.  The result is 10.3 percent slower than the retained fold-structure proof, 25.2 percent faster than the capacity-and-frame screen, and 33.0 percent faster than baseline.  Its 655-line, 2,472-word, 32,143-byte proof is 147 lines longer than the retained proof because the update boundary and three frame getters remain artifact-local.

The experiment establishes that a compact semantic endpoint can prevent heartbeat exhaustion and complete the proof.  It does not establish a proof-time or proof-size improvement over the retained primary proof, so the retained package remains primary.  [Opacity and elaboration boundaries in artifact proofs](../../docs/opacity-proof-boundaries.md) records the mechanism, evidence limits, and planned compiled and out-of-sample tests.

## Compiler-described guarded-back-edge comparison

The [guarded-back-edge package](experiments/guarded-back-edge.proof/) replaces the artifact-local update theorem with a generic compiled ProofKit theorem.  The compiler annotation supplies a versioned scalar descriptor for the fold body and done condition, while the annotation consumer proves that nested loop instructions 16 through 37 equal the generic guarded-back-edge program.  The generated recipe and structured LTG expose that equality, the body and condition evaluator theorems, and `ScalarTransition.guardedBackEdgeProgram_spec` to the proving agent.

The fresh agent selected `guarded-back-edge` on its first structural search and applied the theorem after the checked traversal prefix.  The theorem discharged the wrapping-add body, done condition, successor prefix invariant, and strict remaining-input measure without reducing the WAT update beneath the outer loop postcondition.  Generic evaluation of the continuing index assignment exceeded the simplifier step limit, after which `Stmt.eval_toState` and a finite `U64State` reduction closed the remaining descriptor obligation.

Stage 5 took 1,972.223 seconds, including 1,872.127 seconds in Codex and 79.123 seconds in outer acceptance.  The run is 5.3 percent faster than the retained 2,082.889-second primary and 14.2 percent faster than the local compact-boundary experiment.  Its 589-line, 2,208-word, 31,148-byte proof is 15.9 percent longer than the primary but 10.1 percent shorter than the local compact-boundary proof, and a separate `leanexegen verify -s` run accepted the package.

This single measurement supports theorem applicability, structured retrieval, and a modest proof-time reduction.  A different fold operation will test whether the descriptor boundary transfers without wrapping-sum-specific support, and the generator will first add a compact continuing-transition equation.  The retained root package remains the shorter primary until the out-of-sample result and further timing evidence justify replacement.

## Fold-body composition capability

The [fold-body composition package](experiments/fold-body-composition.proof/) applies the current annotation generator and proof kit to the unchanged Demo 9 artifact.  Its generated recipe supplies the checked continuing-loaded-frame equality and `FixedArrayFoldBody.continuingGuardedProgram_spec`, and independent package verification accepts the exact artifact theorem.  The archived behavioral proof predates the composition theorem, so this package establishes annotation recognition, theorem availability, and package integrity rather than proof-agent retrieval or use; the fresh fixed-artifact reproof measures those claims separately.

## Fold-body composition reproof

The [fresh fold-body reproof](experiments/fold-body-reproof.proof/) selected `fixed-array-fold-body` in its first annotation-driven catalog query and applied `FixedArrayFoldBody.continuingGuardedProgram_spec` to the wrapping-add loop.  The theorem consumed the checked indexed load, generated loaded-frame equality, wrapping-add body evaluator, false done condition, index-increment evaluator, and guarded back edge.  The artifact proof retained the sum-prefix successor equation, invariant reconstruction, and decreasing measure, and a separate `leanexegen verify -s` run accepted the complete package over the unchanged digest.

Stage 5 took 2,074.169 seconds, including 1,984.791 seconds in Codex and 69.416 seconds in outer acceptance.  The run was 8.720 seconds, or 0.4 percent, faster than the 2,082.889-second retained fold-structure proof, 101.946 seconds, or 5.2 percent, slower than the guarded-back-edge screen, and 223.708 seconds, or 9.7 percent, faster than the local compact-boundary screen.  These results establish no proof-time improvement over the theorem's immediate component, but they establish fresh selection and accepted use across wrapping addition and multiplication.

The proof contains 588 lines, 2,484 whitespace-delimited words, and 29,973 bytes.  Compared with the guarded-back-edge proof, it has one fewer line, 276 more words, and 1,175 fewer bytes, so the proof-size evidence is mixed.  The journal also records repeated proof-local frame projections before the singleton suffix and the need to fix the theorem's module, environment, store, and frame arguments when callback inference generalizes them; the structured guidance records both findings, while the shorter root proof remains primary.

## Execution

The first sample exercises wrapping addition in the valid branch.  The second sample exceeds the maximum length and exercises the empty-result branch.  Direct execution of the proved artifact produced these values:

```text
Input: [18446744073709551615, 1]
Output: [0]
Input: [1, 2, 3, 4, 5, 6, 7, 8, 9]
Output: []
```

## Retained files

Every retained root file fixes a generation input, artifact, proof context, or measured result.  The [verification package](program.proof/) contains the complete embedded artifact, generated proof modules, filtered LTG snapshot, tool pins, and package manifest accepted by the independent verifier.  The table identifies each root file and the package directory.

| File | Contents |
|---|---|
| [Generation request](request.txt) | The bounded wrapping-sum behavior supplied to leanexegen. |
| [Formal specification](spec.lean) | The expected result, runtime precondition, and artifact property. |
| [Lean program](program.lean) | The generated source compiled by LeanExe. |
| [WASM module](program.wasm) | The exact executable artifact covered by the proof. |
| [WAT rendering](program.wat) | The textual instruction representation of the artifact. |
| [Behavioral proof](proof.lean) | The accepted proof using the shared fold and array support. |
| [Compiler annotations](program.annotations.json) | The checked bounded-length region emitted by the compiler. |
| [Annotation equality](annotation-matches.lean) | The generated equalities for both capacity prefixes and the complete fold, setup, continuing, and result intervals. |
| [Proof recipe plan](proof-recipes.json) | The length dispatch, capacities, fold invariant, exact subregions, frame projections, and checked execution declarations. |
| [Selected strategy notes](proof-strategies.md) | The feature-selected proof guidance supplied to the agent. |
| [Program feature report](proof-task-features.json) | The instruction, local, operation, annotation, and LTG feature inventory. |
| [Proof journal](proof-journal.md) | The agent's searches, failed checks, proof decisions, and final acceptance. |
| [Proof telemetry](proof-telemetry.json) | The measured Stage 5 intervals and accepted proof identity. |
| [Timing comparison](proof-timings.json) | The baseline and structured-LTG timing and proof-size measurements. |
| [Stage reports](stage-reports.json) | The accepted specification, source, and artifact-proof task reports. |
| [Verification package](program.proof/) | The self-contained package accepted by `leanexegen verify -s`. |
| [Current capacity and frame comparison](experiments/capacity-frame-current.proof/) | The slower structural comparison re-frozen and independently accepted under the current proof kit. |
| [Original capacity and frame generation](experiments/capacity-frame.proof/) | The same accepted proof with the proof-kit identity supplied during its measured generation. |
| [Compact fold-boundary comparison](experiments/compact-fold-boundary.proof/) | The accepted fixed-artifact proof that isolates the post-load update behind a compact continuation-generic theorem. |
| [Compiler-described guarded-back-edge comparison](experiments/guarded-back-edge.proof/) | The accepted fixed-artifact proof that uses the generic guarded-back-edge theorem with compiler-generated transition evidence. |
| [Fold-body composition capability](experiments/fold-body-composition.proof/) | The current annotations, proof kit, and accepted archived proof for the unchanged artifact; its behavioral proof predates the fold-body theorem. |
| [Fresh fold-body composition reproof](experiments/fold-body-reproof.proof/) | The independently verified fixed-artifact proof that retrieved and used the shared composition theorem for wrapping addition. |
