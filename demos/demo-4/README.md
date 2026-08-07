# Bounded Array-Map Artifact Walkthrough

## Summary

This demo is the first held-out test of the shared lemma, tactic, and guidance collection after its development on the three preceding demos.  It asks `leanexegen` to map wrapping addition by one over an input array of at most eight `UInt64` words and to return an empty array for longer inputs.  The request requires a compiled loop instead of eight separately written cases.

The generated artifact contains one reachable 456-instruction function with 16 locals and three loops.  One loop searches the free list for the mapped result, one performs the element transformation, and the oversized-input branch contains a second allocator search for the empty result.  The 1,913-byte WASM module has SHA-256 digest `c538d40936b426ba875b3dae1913e62ff00a44b34adff2adcd70922e5a4c95ff`.

The preexisting annotation and proof-kit system received this artifact without any Demo 4-derived change.  It found no matched proof region or checked composition, so Codex constructed the complete artifact proof from the generic ABI, allocator, memory, and loop guidance.  Stage 5 took 2,364.735 seconds, including 2,255.687 seconds in Codex and 98.593 seconds in independent outer acceptance.

## Program and theorem

The [generation request](request.txt) defines the complete behavior and the required loop implementation.  The [formal specification](spec.lean) uses `Array.map` in its successful branch, and the [generated Lean program](program.lean) implements the same function without importing the specification.  Both generated tasks passed their first outer acceptance checks.

```lean
def expected (input : Array UInt64) : Array UInt64 :=
  if input.size ≤ 8 then
    input.map fun element => element + 1
  else
    #[]
```

The [behavioral proof](proof.lean) proves the formal specification directly for the Talos model of the exact artifact.  Its valid branch proves dynamic allocation, the emitted length store, a prefix invariant for the transformation loop, wrapping addition, and the final array representation.  Its invalid branch proves the allocator and empty-array construction directly because the available allocator theorem requires an exact local-frame length.

## Held-out baseline

The [compiler annotations](program.annotations.json) contain no regions for this function, and the [proof recipe plan](proof-recipes.json) is empty.  The [selected strategy notes](proof-strategies.md) and [program feature report](proof-task-features.json) identify loops, memory, allocation, arithmetic, and a large elaboration boundary, but they provide no checked decomposition of the emitted map.  This makes the retained run a baseline for later annotation and proof-kit iterations rather than a result influenced by Demo 4-specific LTG.

The [proof journal](proof-journal.md) records 27 edited Lean checks before acceptance.  It identifies five repeated boundaries: bounded-length dispatch, dynamic capacity normalization, an allocator inside a larger local frame, a dynamic result-length store, and the transformed-prefix loop invariant.  Those observations determine the next general LTG work while preserving the specification, source, and artifact as fixed test inputs.

The accepted proof contains 457 lines and has SHA-256 digest `6bd050aab0f4e1124e9ed2a2ef6e75a6020e7ab7b90ce82d2315dc0668b08488`.  The [proof telemetry](proof-telemetry.json) records the precise Stage 5 intervals, and the [stage reports](stage-reports.json) record the accepted declarations and source digests for all three generated tasks.  Independent acceptance proved `Artifact.artifact_correct` from the embedded bytes after Codex completed the behavior theorem.

## Execution

The first retained sample checks ordinary wrapping behavior, including `UInt64.max + 1 = 0`.  The second sample contains nine elements and checks the oversized-input branch.  The compiled artifact returned both expected arrays.

```text
Input: [0, 41, 18446744073709551615]
Output: [1, 42, 0]
Input: [1, 2, 3, 4, 5, 6, 7, 8, 9]
Output: []
```

The [captured standard output](stdout.txt) records every stage boundary and both sample results.  The [captured standard error](stderr.txt) records the four trust-boundary warnings.  The [WAT rendering](program.wat) provides the textual form of the retained [WASM module](program.wasm) used to construct the Talos model.

## Retained files

Every retained file either fixes the experiment, records the proof inputs, or records an accepted result.  The annotation, recipe, strategy, feature, and journal files preserve what the baseline agent knew and how it proceeded.  Later iterations can therefore compare both time and proof structure against the same artifact.

| File | Contents |
|---|---|
| [Generation request](request.txt) | The bounded wrapping-map behavior and loop requirement. |
| [Formal specification](spec.lean) | The mathematical array transformation and artifact-level specification. |
| [Lean program](program.lean) | The generated source compiled by LeanExe. |
| [WASM module](program.wasm) | The exact executable artifact covered by the proof. |
| [WAT rendering](program.wat) | The textual instruction representation used for the Talos model. |
| [Behavioral proof](proof.lean) | The accepted direct proof of the generated WASM behavior. |
| [Compiler annotations](program.annotations.json) | The empty region set emitted before loop-oriented annotations existed. |
| [Proof recipe plan](proof-recipes.json) | The empty checked recipe plan supplied to the baseline agent. |
| [Selected strategy notes](proof-strategies.md) | The program-feature-selected proof guidance. |
| [Program feature report](proof-task-features.json) | The reachable instruction, local, loop, memory, arithmetic, and allocation facts. |
| [Proof journal](proof-journal.md) | The agent's chronological account of 27 edited proof checks. |
| [Proof telemetry](proof-telemetry.json) | The measured proof-session and outer-acceptance intervals. |
| [Stage reports](stage-reports.json) | The accepted reports for specification, source, and artifact-proof generation. |
| [Standard output](stdout.txt) | The stage boundaries, sample results, and run command. |
| [Standard error](stderr.txt) | The generated trust-boundary warnings. |
