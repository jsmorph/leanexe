# Bounded Array-Filter Artifact Walkthrough

## Summary

This demo is a second held-out loop case for the shared lemma, tactic, annotation, and guidance work.  It retains values below 100 from an input array of at most eight `UInt64` words, preserving their order, and returns an empty array for a longer input.  The generated source must use `Array.filter`, so the compiled artifact has a value-dependent output length and a loop whose store occurs only on the retained-element branch.

The 1,975-byte WASM module has SHA-256 digest `7c05b423d0cb42b5e8b92fecbefdfc408a2314f2dea7f74bfcbc1674ff96b8de`.  Its generated proof contains 969 lines and has SHA-256 digest `a65e9018ce92e01f3fd8b82e117a237571d0ae88512a682819c2a9fe6c2a4822`.  Independent `leanexegen verify` accepted the archived theorem after rebuilding the formal specification and exact-artifact proof.

Stage 5 took 1,635.679 seconds, including 1,580.641 seconds in Codex and 44.738 seconds in independent outer acceptance.  The proving agent made fourteen edited Lean checks after the deterministic starter failed, then passed its required final build.  The complete generation run took 1,949.512 seconds from stage one through stage eight.

A controlled LTG iteration preserved the specification, source, decoded Program, WASM bytes, artifact theorem, and heap-reserve boundary.  A parameterized filter theorem and exact whole-function annotation produced a three-run Stage 5 median of 90.745 seconds, a 94.5 percent reduction, and reduced the generated proof from 969 lines to 70.  Every deterministic starter passed its first Lean check unchanged, and independent package verification accepted the retained results.

## Program and theorem

The [generation request](request.txt) defines the bound, predicate, stable order, oversized-input behavior, and loop requirement.  The [formal specification](spec.lean) defines the mathematical result and a branch-sensitive heap-reserve bound.  The [generated Lean program](program.lean) implements the same array function without importing the formal specification.

```lean
def expected (input : Array UInt64) : Array UInt64 :=
  if input.size ≤ 8 then
    input.filter fun element => element < (100 : UInt64)
  else
    #[]

def heapReserveBytes (input : Array UInt64) : Nat :=
  if input.size ≤ 8 then
    48 + 8 * (input.size + 1)
  else
    56
```

The [behavioral proof](proof.lean) proves `ArtifactSpec` for the Talos model produced from the exact WASM bytes.  Its main loop invariant represents the output payload as `(input.extract 0 index).filter (· < 100)` and relates the output counter to the size of that filtered prefix.  The retained-element branch proves the conditional store and increments both counters, while the rejected-element branch advances only the input index.

## Resource boundary

The first proof attempt found a counterexample to the former runtime precondition.  That precondition reserved memory from the final result length, so input `[100]` required only the empty-result bound even though the compiled filter allocated input-sized capacity before discovering that it would retain no element.  With the bump pointer at `2^32 - 56` and memory already at 65,536 pages, the precondition held but the allocator could not obtain the additional capacity word and the artifact trapped.

The formal interface now separates final-output representation bounds from `heapReserveBytes input`.  The specification author states a conservative bound on every bump-heap byte consumed above the initial heap top, including headers, reserved capacity, intermediate allocation, and retained allocation.  The source-free artifact proof must derive the allocator premises from that bound, so an underestimate prevents proof acceptance.

Package schema 6 identifies this expanded formal interface.  The verifier continues to accept package schemas 3 through 5 with their previous `RuntimeReady` fields and declaration checks.  Independent tests accepted an existing schema-5 Demo 4 package and this schema-6 Demo 5 package under the same checkout.

## Baseline proof context

The [baseline compiler annotations](baseline-program.annotations.json) contain one exact unsigned length-at-most-eight dispatch.  The [baseline proof recipe plan](baseline-proof-recipes.json) therefore offers only `wp_fixed_array_length_le_dispatch 5, 8`; it contains no filter-loop region or whole-wrapper theorem.  The [baseline strategy notes](baseline-proof-strategies.md) and [baseline program feature report](baseline-proof-task-features.json) identify the loop, memory, allocation, arithmetic, and large elaboration boundary without supplying a checked filter abstraction.

The [proof journal](proof-journal.md) records the agent's progress through exact wrapper decomposition, allocator specialization, loop entry, predicate branching, frame normalization, address bounds, and prefix updates.  Several steps duplicate structure that a parameterized bounded-filter theorem could prove once, including capacity allocation, the output-count invariant, accepted and rejected prefix lemmas, dynamic result-length storage, and empty-result allocation.  These observations provide the baseline for a compiler filter annotation and a deterministic theorem starter while the specification, source, and artifact remain fixed.

The [proof telemetry](proof-telemetry.json) records the measured Stage 5 intervals and accepted proof digest.  The [stage reports](stage-reports.json) retain the accepted source identities, task decisions, and outer diagnostics for all three generated tasks.  Together with the exact proof and WASM, these records support controlled reproof timing after the shared filter support exists.

## Complete filter-wrapper iteration

`Project.ProofKit.FixedArrayFilterLt.wrapperProgram_spec` proves the compiler's canonical bounded stable filter for arbitrary maximum size and unsigned threshold.  The checked theorem contains the bounded-length dispatch, input-sized capacity calculation, valid and empty allocations, predicate decisions, conditional payload stores, filtered-prefix loop invariant, dynamic result-length store, and public return.  Its `heapReserveBytes` function matches the branch-sensitive allocation bound required by the schema-6 artifact specification.

The compiler recognizes the exact extracted form `if input.size ≤ n then input.filter (fun element ⇒ element < t) else #[]`.  The current [compiler annotations](program.annotations.json) cover the complete decoded function with `leanexe.array.filter-lt.v1` and retain the nested bounded-length dispatch.  The current [proof recipe plan](proof-recipes.json) names `wrapperProgram_spec` and the generated `AnnotationMatches` equality that Lean reduced to `wrapperProgram 8 100` for this artifact.

The accepted [filter-composition proof](filter-proof.lean) contains 70 lines and has SHA-256 digest `9664bb3f113379d95a4dc64c010db7b5ac3ae139795da82d9bca0d366bc03667`.  Its first [journal](filter-proof-journal.md) and [telemetry](filter-proof-telemetry.json) record a successful initial check with no edit or repeated check, 53.260 seconds in Codex, 24.483 seconds in outer acceptance, and 86.795 seconds from Stage 5 start to first acceptance.  The [filter run stage reports](filter-stage-reports.json) retain the accepted source identity and diagnostic for that controlled proof task.

Two further runs produced the same proof and artifact digests.  Their [second journal](filter-proof-r2-journal.md) and [third journal](filter-proof-r3-journal.md) again record successful unchanged starters, while their [second telemetry](filter-proof-r2-telemetry.json) and [third telemetry](filter-proof-r3-telemetry.json) report 90.745 and 95.718 seconds.  The three-run median is 90.745 seconds, and the range is 8.923 seconds.

The [timing comparison](filter-proof-comparison.json) records a 1,544.934-second reduction from the 1,635.679-second baseline to the three-run median, or 94.5 percent.  It also records an 899-line reduction, or 92.8 percent, although completed proof time remains the primary measure.  Every retained run uses the 1,975-byte artifact with digest `7c05b423d0cb42b5e8b92fecbefdfc408a2314f2dea7f74bfcbc1674ff96b8de`, and independent `leanexegen verify` accepted the first and third final packages.

## Execution

The first sample includes retained values, a boundary value, zero, and `UInt64.max`.  The second sample contains nine elements and exercises the oversized-input branch.  The compiled artifact returned both expected arrays.

```text
Input: [99, 100, 0, 18446744073709551615]
Output: [99, 0]
Input: [1, 2, 3, 4, 5, 6, 7, 8, 9]
Output: []
```

The [captured standard output](stdout.txt) records every stage boundary, both sample results, and the standalone invocation.  The [captured standard error](stderr.txt) records the four trust-boundary warnings.  The [WAT rendering](program.wat) provides the textual instruction representation of the retained [WASM module](program.wasm).

## Retained files

Every retained file fixes an experiment input, records one of the two proof contexts, or preserves an accepted result.  Files with a `baseline-` prefix show what checked assistance the first agent received, while the unprefixed annotation and guidance files describe the complete filter-wrapper run.  The two accepted proofs, journals, measurements, and shared artifact permit direct comparison.

| File | Contents |
|---|---|
| [Generation request](request.txt) | The bounded stable-filter behavior and loop requirement. |
| [Formal specification](spec.lean) | The mathematical result, heap-reserve function, runtime precondition, and artifact property. |
| [Lean program](program.lean) | The generated source compiled by LeanExe. |
| [WASM module](program.wasm) | The exact executable artifact covered by the proof. |
| [WAT rendering](program.wat) | The textual instruction representation used for the Talos model. |
| [Behavioral proof](proof.lean) | The accepted direct proof of the generated WASM behavior. |
| [Filter-composition proof](filter-proof.lean) | The unchanged deterministic proof using the complete filter theorem. |
| [Baseline compiler annotations](baseline-program.annotations.json) | The bounded-length dispatch and absence of a filter region in the first run. |
| [Baseline proof recipe plan](baseline-proof-recipes.json) | The dispatch-only checked plan supplied to the first proving agent. |
| [Baseline strategy notes](baseline-proof-strategies.md) | The feature-selected guidance supplied to the first proving agent. |
| [Baseline feature report](baseline-proof-task-features.json) | The structural facts and guidance identity supplied to the first proving agent. |
| [Compiler annotations](program.annotations.json) | The complete filter wrapper and nested bounded-length dispatch. |
| [Proof recipe plan](proof-recipes.json) | The complete wrapper theorem and nested dispatch recipe. |
| [Selected strategy notes](proof-strategies.md) | The final feature-selected guidance supplied with the checked recipe. |
| [Program feature report](proof-task-features.json) | The final reachable instruction, local, loop, memory, arithmetic, allocation, and annotation facts. |
| [Proof journal](proof-journal.md) | The agent's chronological account of fourteen edited proof checks. |
| [Proof telemetry](proof-telemetry.json) | The measured proof-session and outer-acceptance intervals. |
| [Stage reports](stage-reports.json) | The accepted reports for specification, source, and artifact-proof generation. |
| [Filter-composition journal](filter-proof-journal.md) | The controlled agent's successful first-check record. |
| [Filter-composition telemetry](filter-proof-telemetry.json) | The controlled run's Stage 5, Codex, and outer-acceptance intervals. |
| [Filter-composition stage reports](filter-stage-reports.json) | The accepted task report and source identity for the controlled run. |
| [Second filter journal](filter-proof-r2-journal.md) | The second final-configuration agent's unchanged-starter record. |
| [Second filter telemetry](filter-proof-r2-telemetry.json) | The second final-configuration Stage 5 intervals. |
| [Third filter journal](filter-proof-r3-journal.md) | The third final-configuration agent's unchanged-starter record. |
| [Third filter telemetry](filter-proof-r3-telemetry.json) | The third final-configuration Stage 5 intervals. |
| [Timing comparison](filter-proof-comparison.json) | The fixed-artifact baseline, complete theorem result, and measured reductions. |
| [Standard output](stdout.txt) | The stage boundaries, sample results, and run command. |
| [Standard error](stderr.txt) | The generated trust-boundary warnings. |
