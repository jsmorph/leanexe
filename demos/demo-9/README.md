# Bounded wrapping-sum artifact walkthrough

## Summary

This demo accepts an `Array UInt64`.  An input containing at most eight elements returns a singleton array whose element is the wrapping sum of the input.  A longer input returns an empty array.

The 1,979-byte WASM module has SHA-256 digest `aa263bbfa89c333f9fab497f1a2c370f476afc3419015d17b368cb7c8a6086d5`.  Its valid branch allocates a singleton result and traverses the input with an emitted loop, while its invalid branch allocates an empty result.  Independent `leanexegen verify -s` accepted the complete package and exact artifact theorem.

The baseline proof completed Stage 5 in 3,431.870 seconds and contained 493 lines.  The annotation-assisted structured-LTG proof completed in 3,188.251 seconds and contained 416 lines, reducing measured time by 7.1 percent and proof length by 77 lines.  The previous fold-prefix attempt took 4,055.765 seconds and 475 lines, so the accepted annotation run also reduced its time by 21.4 percent and its proof by 59 lines.

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

The [compiler annotations](program.annotations.json) identify the bounded array-length dispatch and the nested array-fold region.  The [annotation equality](annotation-matches.lean) names the decoded fold interval at instructions 39 through 65 of the valid branch, then identifies its 16-instruction continuing guard-and-load prefix with `FixedArrayTraversalInput.continuingProgram`.  Lean proves both equalities by reduction, while the consumer checks the reported accumulator, item, index, effective-stop, staging, scratch, guard, element-address load, back-edge, and result-local roles against the decoded artifact.

The [proof recipe plan](proof-recipes.json) names `FixedArrayLengthDispatch.leProgram_spec`, both exact fold-program equalities, `FixedArrayTraversalInput.continuingProgram_spec`, and the generic fold-prefix declarations.  The [selected strategy notes](proof-strategies.md) and [program feature report](proof-task-features.json) provide the structured LTG catalog, allocator guidance, array-framing guidance, and fold invariant.  The retained measured proof predates the traversal theorem, so its 7.1-percent time reduction does not measure that theorem; a later fixed-artifact reproof can test whether the smaller loop-step boundary reduces search.

The [behavioral proof](proof.lean) uses `ArrayFold.foldPrefix` as the loop-carried mathematical coordinate.  It applies `foldPrefix_succ` at the back edge and `foldPrefix_size` at loop exit, while `input_preserved_by_alloc`, `write64After`, and `generatedElement` preserve and read the represented input through result allocation.  The proof also applies the shifted allocator theorem to both result branches and proves each load and store against the exact decoded program.

The [proof journal](proof-journal.md) records the successful path and the failed intermediate approaches.  Broad allocator simplification exhausted the theorem heartbeat, while the `_from hArray` dispatch tactic, opt-in allocator-list tactics, focused instruction reduction, and named post-allocation states produced stable boundaries.  The journal also records that structured retrieval could not find `generatedElement` even though the theorem was available in the supplied proof kit, which led to its addition to the array-memory LTG entry.

The [proof telemetry](proof-telemetry.json), [timing comparison](proof-timings.json), and [stage reports](stage-reports.json) preserve time intervals and source identities.  The annotation-assisted proof has 416 lines, 1,848 whitespace-delimited words, and 17,797 bytes, compared with the baseline's 493 lines, 1,844 words, and 16,312 bytes.  Its longer declaration names record shared theorem use, while the line reduction and 7.1-percent time reduction provide the relevant structural and timing evidence.

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
| [Annotation equality](annotation-matches.lean) | The generated equalities for the complete fold interval and its continuing guard-and-load prefix. |
| [Proof recipe plan](proof-recipes.json) | The length dispatch, fold invariant, exact prefix, and dynamic traversal declarations. |
| [Selected strategy notes](proof-strategies.md) | The feature-selected proof guidance supplied to the agent. |
| [Program feature report](proof-task-features.json) | The instruction, local, operation, annotation, and LTG feature inventory. |
| [Proof journal](proof-journal.md) | The agent's searches, failed checks, proof decisions, and final acceptance. |
| [Proof telemetry](proof-telemetry.json) | The measured Stage 5 intervals and accepted proof identity. |
| [Timing comparison](proof-timings.json) | The baseline and structured-LTG timing and proof-size measurements. |
| [Stage reports](stage-reports.json) | The accepted specification, source, and artifact-proof task reports. |
| [Verification package](program.proof/) | The self-contained package accepted by `leanexegen verify -s`. |
