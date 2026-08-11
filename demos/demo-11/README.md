# Bounded XOR-fold artifact walkthrough

## Summary

This demo accepts an `Array UInt64`.  An input containing at most eight elements returns a singleton array whose element is the bitwise XOR of the input from left to right, starting with zero.  A longer input returns an empty array.

The compiler produced a 1,979-byte WASM module with SHA-256 digest `4f56fd45fe246f3199dc81169235aa0673659b3b2e82e4beeb4c1d910501bd64`.  The artifact theorem proves the specified behavior directly from those bytes under the pinned Talos semantics.  Independent `leanexegen verify -s` accepted the retained package.

Demo 11 tests fold annotations, shared ProofKit theorems, structured LTG retrieval, and the residual-goal retrieval checkpoint on an operation that did not motivate those components.  The proof uses compiler-generated frame accessors and the generic fold-body and singleton-result theorems with a bitwise-XOR scalar descriptor.  The result establishes cross-operation applicability while recording a slower and larger proof-generation run.

## Program and specification

The [generation request](request.txt) fixes the public behavior, maximum input length, XOR identity, and required traversal loop.  The [formal specification](spec.lean) defines the expected array, branch-sensitive heap reserve, runtime precondition, and artifact property.  The [generated Lean program](program.lean) implements the bounded branch with `Array.foldl`.

```lean
def compute (input : Array UInt64) : Array UInt64 :=
  if input.size ≤ 8 then
    #[input.foldl (fun acc value => UInt64.xor acc value) 0]
  else
    #[]
```

The [WASM module](program.wasm) is the executable covered by the theorem.  The [WAT rendering](program.wat) exposes the length dispatch, allocator branches, forward traversal loop, `i64.xor` accumulator update, and result stores.  `wasm-tools` 1.251.0 produced the 20,031-byte rendering from the frozen module.

## Artifact proof

The [compiler annotations](program.annotations.json) identify the unsigned length dispatch and array-fold region.  The [generated annotation equalities](annotation-matches.lean) prove the exact instruction intervals, scalar XOR evaluator, loop continuation, singleton suffix, frame shape, and combined-local getters.  The [proof recipe](proof-recipes.json) publishes these declarations with the generic ProofKit theorems.

The [behavioral proof](proof.lean) uses `ArrayFold.foldPrefix input UInt64.xor 0 index` as its mathematical loop coordinate.  `FixedArrayFoldBody.continuingGuardedProgram_spec` composes the indexed load, generated XOR transition, condition, index increment, and guarded back edge.  `ArrayFold.foldPrefix_succ` proves the invariant update, while the input-size suffix measure proves termination.

The proof isolates the completed fold in `xorSingleton_spec`.  That theorem uses the generated parameter, local-length, value-stack, accumulator, and root accessors with `FixedArrayFold.resultFrame_get_result`, `resultFrame_get_of_ne`, and `singletonResultProgram_spec`.  The accepted source declares no frame-projection theorem.

The [proof journal](proof-journal.md) records a retrieval checkpoint each time the residual goal changed.  For the capacity-frame projection, the agent searched the recipe and LTG, found no exact accessor, and then reduced the concrete definition.  For the fold exit, loop measure, and singleton suffix, it selected and used the generated accessors before attempting local projection facts.

## Measurement

The [proof telemetry](proof-telemetry.json) records 2,452.384 seconds from the start of Stage 5 to the first accepted proof.  Codex used 2,362.386 seconds, and outer acceptance used 77.910 seconds.  The UTC interval and monotonic total agree within one millisecond.

The accepted proof contains 676 lines, 2,798 whitespace-delimited words, and 34,648 bytes.  It took 353.147 seconds, or 16.8 percent, longer than the Demo 10 frame-accessor run and 221.515 seconds, or 9.9 percent, longer than the Demo 9 frame-accessor run.  Those programs have different accumulator operations and proof histories, so the [timing record](proof-timings.json) classifies both comparisons as descriptive.

The proof is 76 lines and 4,080 bytes larger than the Demo 10 accessor proof.  Its extra declarations isolate the public continuation and singleton suffix after the complete loop assertion remained expensive.  The result supports retrieval and theorem applicability but supplies negative proof-time and proof-size evidence.

The first end-to-end invocation ended before a Lean target ran because the independent formal-specification check timed out waiting for the machine-wide Lean slot.  A second invocation acquired the slot and produced the retained package.  The Stage 5 measurement belongs only to that successful invocation.

## Fold-completion adapter experiment

The [fold-completion package](experiments/fold-completion.proof/) preserves an independently verified substitution, and its [manual proof](experiments/manual-fold-completion.lean) applies the annotation-generated `function_0_array_fold_0_singleton_result_spec` theorem directly to the public valid-branch postcondition.  The generated theorem checks the exact singleton-result instruction suffix and supplies the local-layout, result-placement, root-preservation, and destination-validity facts required by the generic `FixedArrayFold.singletonResultProgram_spec_to`.  `Project.ProofKit.Frame.ext` identifies the values-cleared traversal frame with the equivalent exit frame.

The complete artifact theorem passed against the unchanged WASM digest.  The proof decreased from 676 to 580 lines, from 2,798 to 2,350 whitespace-delimited words, and from 34,648 to 30,182 bytes.  It removes the proof-local `xorSingleton_spec` and its separate postcondition consequence while retaining the XOR-prefix equation and represented-singleton proof.

This manual substitution establishes that the generated boundary fits an independently accepted artifact proof.  It contains no fresh proof-generation timing because an agent did not generate the edited source from the proving task.  A controlled reproof will measure whether structured retrieval and the smaller semantic interface reduce construction work.

## Execution

The first sample exercises all four input elements and produces the XOR value 15.  The second sample exceeds the length bound and produces the empty result.  Direct execution of the proved artifact returned these arrays.

```text
Input: [1, 2, 4, 8]
Output: [15]
Input: [1, 2, 3, 4, 5, 6, 7, 8, 9]
Output: []
```

## Retained files

The root files provide readable views of each generation and proof stage.  The [verification package](program.proof/) preserves the embedded artifact, generated proof modules, LTG snapshot, tool pins, journal, telemetry, and package manifest accepted by the independent verifier.  The table identifies every retained root file and the package directory.

| File | Contents |
|---|---|
| [Generation request](request.txt) | The bounded XOR-fold behavior supplied to leanexegen. |
| [Formal specification](spec.lean) | The expected result, runtime precondition, and exact artifact property. |
| [Lean program](program.lean) | The generated source compiled by LeanExe. |
| [WASM module](program.wasm) | The exact executable artifact covered by the proof. |
| [WAT rendering](program.wat) | The textual instruction representation produced by the pinned wasm-tools. |
| [Behavioral proof](proof.lean) | The accepted direct proof of the artifact behavior. |
| [Compiler annotations](program.annotations.json) | The compiler-emitted structural descriptions consumed by the matcher. |
| [Annotation equalities](annotation-matches.lean) | The exact-region, frame-accessor, and scalar-evaluator theorems. |
| [Proof recipe](proof-recipes.json) | The generated direct recipes, accessors, and supporting declarations. |
| [Selected strategies](proof-strategies.md) | The artifact-selected proof guidance supplied to the agent. |
| [Program features](proof-task-features.json) | The program facts that selected the strategy sections. |
| [Proof journal](proof-journal.md) | The agent's searches, diagnostics, decisions, and residual-goal checkpoints. |
| [Proof telemetry](proof-telemetry.json) | The Stage 5 timing intervals and accepted source digest. |
| [Timing record](proof-timings.json) | The held-out measurement and descriptive comparisons. |
| [Stage reports](stage-reports.json) | The accepted specification, source, and artifact-proof reports. |
| [Verification package](program.proof/) | The self-contained package accepted by `leanexegen verify -s`. |
| [Fold-completion package](experiments/fold-completion.proof/) | The independently verified manual proof using the generated exact singleton-result adapter. |
| [Manual fold-completion proof](experiments/manual-fold-completion.lean) | The checked substitution using the generated exact suffix adapter and general local-frame equality theorem. |
