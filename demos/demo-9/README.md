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

The [compiler annotations](program.annotations.json) identify the bounded array-length dispatch and the nested array-fold region.  The [annotation equality](annotation-matches.lean) names the decoded fold interval at instructions 39 through 65 of the valid branch.  It also identifies the setup interval through instruction 62, the 16-instruction continuing guard-and-load prefix inside the loop, and the accumulator-to-result transfer at instructions 63 through 65.  Lean proves the four equalities by reduction, while the consumer checks the reported accumulator, item, index, effective-stop, staging, scratch, guard, element-address load, back-edge, and result-local roles against the decoded artifact.

The [proof recipe plan](proof-recipes.json) names `FixedArrayLengthDispatch.leProgram_spec`, all four exact fold-program equalities, `FixedArrayFold.forwardSetupProgram_spec`, `FixedArrayTraversalInput.continuingProgram_spec`, `FixedArrayFold.resultProgram_spec`, and the generic fold-prefix declarations.  The [selected strategy notes](proof-strategies.md) and [program feature report](proof-task-features.json) provide the structured LTG catalog, allocator guidance, array-framing guidance, and fold invariant.  The measured proof retrieved these entries from the task-specific LTG view and used each of the three fold subregion theorems.

The [behavioral proof](proof.lean) uses `ArrayFold.foldPrefix` as the loop-carried mathematical coordinate.  It applies the checked fold-setup theorem before the invariant, the traversal theorem in the continuing case, `foldPrefix_succ` at the back edge, and the checked result-placement theorem after exit.  The proof also applies the shifted allocator theorem, length-store theorem, payload-store theorem, and final array-representation theorems to the exact decoded program.

The [proof journal](proof-journal.md) records the successful path and each rejected intermediate reduction.  Structured retrieval selected the generic dispatch, fold, traversal, result, allocation, and memory entries while excluding artifact-specific worked examples.  The journal identifies two remaining general gaps: the result-capacity prefix lacks a parameterized theorem, and loop invariants need a concise way to turn `Locals.get` facts into internal-list getter facts.

The [proof telemetry](proof-telemetry.json), [timing comparison](proof-timings.json), and [stage reports](stage-reports.json) preserve time intervals and source identities.  The retained proof has 508 lines, 2,155 whitespace-delimited words, and 24,327 bytes, compared with 416 lines, 1,848 words, and 17,797 bytes in the preceding annotation run.  Its 34.7-percent time reduction accompanies a 22.1-percent line increase, so the result supports faster proof generation and better shared-boundary use while recording a proof-size cost for the next LTG iteration.

## Capacity and frame comparison

The [current accepted comparison package](experiments/capacity-frame-current.proof/) holds the specification, source, and WASM fixed while adding exact capacity-prefix equalities, `FixedArrayCapacity.constantProgram_spec`, and the structured LTG.  Independent verification accepted its artifact theorem under the current proof-kit identity; the [original generation package](experiments/capacity-frame.proof/) preserves the proof kit supplied during generation.  Its monotonic Stage 5 measurement was 3,070.994 seconds, 47.4 percent slower than the retained fold-structure proof, while remaining 3.7 percent faster than the earlier fold-annotation proof and 10.5 percent faster than the baseline.

The comparison proof contains 642 lines, 2,524 words, and 30,858 bytes.  It uses the shared capacity theorem in both length branches and reaches the checked setup, traversal, result-placement, allocator, and result-store boundaries, but it adds local theorems for the traversal exit edge, the accumulator/index update, and two getters from the updated frame.  The exit edge and final root transfer have since become checked ProofKit theorems, and traversal guidance now names the shared combined-to-internal frame projection; the accumulator/index update remains a candidate compiler motif rather than a promoted general theorem.

The telemetry's UTC timestamps span 12,764.900 seconds, while its monotonic Stage 5 measurement records 3,070.994 seconds.  The 9,693.906-second difference occurred outside the monotonic interval, and the accessible system journal did not identify its cause.  Timing comparisons therefore use the telemetry's monotonic total, while `proof-timings.json` preserves both measurements.

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
| [Annotation equality](annotation-matches.lean) | The generated equalities for the complete fold, setup, continuing, and result intervals. |
| [Proof recipe plan](proof-recipes.json) | The length dispatch, fold invariant, exact subregions, and checked execution declarations. |
| [Selected strategy notes](proof-strategies.md) | The feature-selected proof guidance supplied to the agent. |
| [Program feature report](proof-task-features.json) | The instruction, local, operation, annotation, and LTG feature inventory. |
| [Proof journal](proof-journal.md) | The agent's searches, failed checks, proof decisions, and final acceptance. |
| [Proof telemetry](proof-telemetry.json) | The measured Stage 5 intervals and accepted proof identity. |
| [Timing comparison](proof-timings.json) | The baseline and structured-LTG timing and proof-size measurements. |
| [Stage reports](stage-reports.json) | The accepted specification, source, and artifact-proof task reports. |
| [Verification package](program.proof/) | The self-contained package accepted by `leanexegen verify -s`. |
| [Current capacity and frame comparison](experiments/capacity-frame-current.proof/) | The slower structural comparison re-frozen and independently accepted under the current proof kit. |
| [Original capacity and frame generation](experiments/capacity-frame.proof/) | The same accepted proof with the proof-kit identity supplied during its measured generation. |
