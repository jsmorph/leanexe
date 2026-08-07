# Bounded Array-Map Artifact Walkthrough

## Summary

This demo is the first held-out test of the shared lemma, tactic, and guidance collection after its development on the three preceding demos.  It asks `leanexegen` to map wrapping addition by one over an input array of at most eight `UInt64` words and to return an empty array for longer inputs.  The request requires a compiled loop instead of eight separately written cases.

The generated artifact contains one reachable 456-instruction function with 16 locals and three loops.  One loop searches the free list for the mapped result, one performs the element transformation, and the oversized-input branch contains a second allocator search for the empty result.  The 1,913-byte WASM module has SHA-256 digest `c538d40936b426ba875b3dae1913e62ff00a44b34adff2adcd70922e5a4c95ff`.

The preexisting annotation and proof-kit system received this artifact without any Demo 4-derived change.  It found no matched proof region or checked composition, so Codex constructed the complete artifact proof from the generic ABI, allocator, memory, and loop guidance.  Stage 5 took 2,364.735 seconds, including 2,255.687 seconds in Codex and 98.593 seconds in independent outer acceptance.

Two LTG iterations preserved the specification, source, decoded Program, WASM bytes, and artifact theorem.  Generalizing the allocator window reduced Stage 5 to 1,191.695 seconds, after which a parameterized whole-wrapper theorem and exact compiler annotation reduced it to 103.123 seconds.  The final deterministic starter passed its first Lean check unchanged and independent package verification accepted the result.

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

The [baseline compiler annotations](baseline-program.annotations.json) contain no regions for this function, and the [baseline proof recipe plan](baseline-proof-recipes.json) is empty.  The [baseline strategy notes](baseline-proof-strategies.md) and [baseline program feature report](baseline-proof-task-features.json) identify loops, memory, allocation, arithmetic, and a large elaboration boundary, but they provide no checked decomposition of the emitted map.  This makes the retained run a baseline for later annotation and proof-kit iterations rather than a result influenced by Demo 4-derived LTG.

The [proof journal](proof-journal.md) records 27 edited Lean checks before acceptance.  It identifies five repeated boundaries: bounded-length dispatch, dynamic capacity normalization, an allocator inside a larger local frame, a dynamic result-length store, and the transformed-prefix loop invariant.  Those observations determine the next general LTG work while preserving the specification, source, and artifact as fixed test inputs.

The accepted proof contains 457 lines and has SHA-256 digest `6bd050aab0f4e1124e9ed2a2ef6e75a6020e7ab7b90ce82d2315dc0668b08488`.  The [proof telemetry](proof-telemetry.json) records the precise Stage 5 intervals, and the [stage reports](stage-reports.json) record the accepted declarations and source digests for all three generated tasks.  Independent acceptance proved `Artifact.artifact_correct` from the embedded bytes after Codex completed the behavior theorem.

## Allocator-window iteration

The first LTG iteration generalized `FixedArrayAllocatorWindow.region_spec` to accept unused locals after its allocator scratch window.  A controlled `leanexegen reprove` run held the specification, source, WASM, decoded Program, and artifact theorem fixed while exposing the revised proof kit and guidance to a new Codex session.  The resulting [allocator-window proof](allocator-proof.lean) applies the shared theorem to both the successful map allocation and the oversized-input empty-result allocation.

Stage 5 fell from 2,364.735 seconds to 1,191.695 seconds, a reduction of 1,173.040 seconds, or 49.6 percent.  Codex time fell from 2,255.687 seconds to 1,154.873 seconds, while independent outer acceptance fell from 98.593 seconds to 25.963 seconds.  The [iteration telemetry](allocator-proof-telemetry.json) records the measured intervals, and the [iteration journal](allocator-proof-journal.md) records nineteen edited checks before acceptance.

The journal shows that the new theorem removed the direct proof of the invalid branch's allocator, which occupied the last ten baseline iterations.  The controlled run still spent ten checks reaching the successful allocator and seven checks establishing the map loop and its transformed-prefix invariant.  Those remaining compiler templates motivate the bounded-dispatch, capacity, map-loop, and annotation work in the next iteration.

## Complete map-wrapper iteration

`FixedArrayMapAdd.wrapperProgram_spec` proves the compiler's canonical bounded wrapping-add map for arbitrary maximum size and addend.  Its checked body contains the bounded-length dispatch, capacity normalization, both allocations, dynamic result-length store, transformed-prefix loop invariant, payload stores, and public return.  The compiler emits a whole-function `leanexe.array.map-add.v1` region only for the exact corresponding extracted IR shape.

The current [compiler annotations](program.annotations.json) record the complete map wrapper and its nested bounded-length dispatch.  The [proof recipe plan](proof-recipes.json) names `wrapperProgram_spec` and a generated `AnnotationMatches` theorem that Lean reduced to equality with `wrapperProgram 8 1`.  The current [selected strategy notes](proof-strategies.md) and [program feature report](proof-task-features.json) accompanied this checked recipe in the controlled proof task.

The accepted [map-wrapper proof](map-proof.lean) contains 66 lines and has SHA-256 digest `bf07793985539b6c0a7e9076c97f836050c859b47b13ab3f70a3383270b29d56`.  Its [journal](map-proof-journal.md) records one successful initial check, no proof edit, and no repeated in-session check, while its [telemetry](map-proof-telemetry.json) records 66.734 seconds in Codex, 27.688 seconds in outer acceptance, and 103.123 seconds from Stage 5 start to first acceptance.  The [map run stage reports](map-stage-reports.json) identify the accepted declarations and confirm that the deterministic starter remained unchanged.

The final Stage 5 time is 2,261.612 seconds, or 95.6 percent, below the held-out baseline and 1,088.572 seconds, or 91.3 percent, below the allocator-window iteration.  The proof is 391 lines, or 85.6 percent, shorter than the baseline, although proof length remains secondary to completed proof time.  Independent `leanexegen verify` accepted the final package, and both retained WASM copies have digest `c538d40936b426ba875b3dae1913e62ff00a44b34adff2adcd70922e5a4c95ff`.

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

Every retained file either fixes the experiment, records the proof inputs, or records an accepted result.  Files with a `baseline-` prefix preserve what the first agent knew, while the unprefixed annotation and guidance files describe the final whole-wrapper run.  The three accepted proofs and their measurements permit direct comparison against the same artifact.

| File | Contents |
|---|---|
| [Generation request](request.txt) | The bounded wrapping-map behavior and loop requirement. |
| [Formal specification](spec.lean) | The mathematical array transformation and artifact-level specification. |
| [Lean program](program.lean) | The generated source compiled by LeanExe. |
| [WASM module](program.wasm) | The exact executable artifact covered by the proof. |
| [WAT rendering](program.wat) | The textual instruction representation used for the Talos model. |
| [Behavioral proof](proof.lean) | The accepted direct proof of the generated WASM behavior. |
| [Allocator-window proof](allocator-proof.lean) | The controlled proof generated with the generalized allocator theorem. |
| [Allocator-window journal](allocator-proof-journal.md) | The controlled agent's chronological account of nineteen edited checks. |
| [Allocator-window telemetry](allocator-proof-telemetry.json) | The controlled run's measured proof-session and outer-acceptance intervals. |
| [Map-wrapper proof](map-proof.lean) | The unchanged deterministic proof using the complete checked theorem. |
| [Map-wrapper journal](map-proof-journal.md) | The final agent's record of its successful first check. |
| [Map-wrapper telemetry](map-proof-telemetry.json) | The final run's Stage 5, Codex, and outer-acceptance intervals. |
| [Map-wrapper stage reports](map-stage-reports.json) | The accepted task report and source identities for the final run. |
| [Baseline compiler annotations](baseline-program.annotations.json) | The empty region set emitted before loop-oriented annotations existed. |
| [Baseline proof recipe plan](baseline-proof-recipes.json) | The empty checked recipe plan supplied to the baseline agent. |
| [Baseline strategy notes](baseline-proof-strategies.md) | The feature-selected guidance supplied to the baseline agent. |
| [Baseline feature report](baseline-proof-task-features.json) | The structural facts and guidance identity supplied to the baseline agent. |
| [Compiler annotations](program.annotations.json) | The checked whole-map and bounded-dispatch regions used in the final run. |
| [Proof recipe plan](proof-recipes.json) | The complete wrapper theorem and nested dispatch recipe. |
| [Selected strategy notes](proof-strategies.md) | The final program-feature-selected proof guidance. |
| [Program feature report](proof-task-features.json) | The final reachable instruction, local, loop, memory, arithmetic, and allocation facts. |
| [Proof journal](proof-journal.md) | The agent's chronological account of 27 edited proof checks. |
| [Proof telemetry](proof-telemetry.json) | The measured proof-session and outer-acceptance intervals. |
| [Stage reports](stage-reports.json) | The accepted reports for specification, source, and artifact-proof generation. |
| [Standard output](stdout.txt) | The stage boundaries, sample results, and run command. |
| [Standard error](stderr.txt) | The generated trust-boundary warnings. |
