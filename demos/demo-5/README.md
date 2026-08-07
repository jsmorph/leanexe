# Bounded Array-Filter Artifact Walkthrough

## Summary

This demo is a second held-out loop case for the shared lemma, tactic, annotation, and guidance work.  It retains values below 100 from an input array of at most eight `UInt64` words, preserving their order, and returns an empty array for a longer input.  The generated source must use `Array.filter`, so the compiled artifact has a value-dependent output length and a loop whose store occurs only on the retained-element branch.

The 1,975-byte WASM module has SHA-256 digest `7c05b423d0cb42b5e8b92fecbefdfc408a2314f2dea7f74bfcbc1674ff96b8de`.  Its generated proof contains 969 lines and has SHA-256 digest `a65e9018ce92e01f3fd8b82e117a237571d0ae88512a682819c2a9fe6c2a4822`.  Independent `leanexegen verify` accepted the archived theorem after rebuilding the formal specification and exact-artifact proof.

Stage 5 took 1,635.679 seconds, including 1,580.641 seconds in Codex and 44.738 seconds in independent outer acceptance.  The proving agent made fourteen edited Lean checks after the deterministic starter failed, then passed its required final build.  The complete generation run took 1,949.512 seconds from stage one through stage eight.

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

The [compiler annotations](program.annotations.json) contain one exact unsigned length-at-most-eight dispatch.  The [proof recipe plan](proof-recipes.json) therefore offers only `wp_fixed_array_length_le_dispatch 5, 8`; it contains no filter-loop region or whole-wrapper theorem.  The [selected strategy notes](proof-strategies.md) and [program feature report](proof-task-features.json) identify the loop, memory, allocation, arithmetic, and large elaboration boundary without supplying a checked filter abstraction.

The [proof journal](proof-journal.md) records the agent's progress through exact wrapper decomposition, allocator specialization, loop entry, predicate branching, frame normalization, address bounds, and prefix updates.  Several steps duplicate structure that a parameterized bounded-filter theorem could prove once, including capacity allocation, the output-count invariant, accepted and rejected prefix lemmas, dynamic result-length storage, and empty-result allocation.  These observations provide the baseline for a compiler filter annotation and a deterministic theorem starter while the specification, source, and artifact remain fixed.

The [proof telemetry](proof-telemetry.json) records the measured Stage 5 intervals and accepted proof digest.  The [stage reports](stage-reports.json) retain the accepted source identities, task decisions, and outer diagnostics for all three generated tasks.  Together with the exact proof and WASM, these records support controlled reproof timing after the shared filter support exists.

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

Every retained file fixes an experiment input, records the proof context, or preserves an accepted result.  The annotations and recipe plan show what checked assistance the baseline agent received.  The proof, journal, telemetry, and stage reports record what remained for the agent and how long acceptance took.

| File | Contents |
|---|---|
| [Generation request](request.txt) | The bounded stable-filter behavior and loop requirement. |
| [Formal specification](spec.lean) | The mathematical result, heap-reserve function, runtime precondition, and artifact property. |
| [Lean program](program.lean) | The generated source compiled by LeanExe. |
| [WASM module](program.wasm) | The exact executable artifact covered by the proof. |
| [WAT rendering](program.wat) | The textual instruction representation used for the Talos model. |
| [Behavioral proof](proof.lean) | The accepted direct proof of the generated WASM behavior. |
| [Compiler annotations](program.annotations.json) | The exact bounded-length dispatch emitted for the artifact. |
| [Proof recipe plan](proof-recipes.json) | The checked dispatch tactic offered to the proving agent. |
| [Selected strategy notes](proof-strategies.md) | The feature-selected proof guidance supplied to the proving agent. |
| [Program feature report](proof-task-features.json) | The reachable instruction, local, loop, memory, arithmetic, allocation, and annotation facts. |
| [Proof journal](proof-journal.md) | The agent's chronological account of fourteen edited proof checks. |
| [Proof telemetry](proof-telemetry.json) | The measured proof-session and outer-acceptance intervals. |
| [Stage reports](stage-reports.json) | The accepted reports for specification, source, and artifact-proof generation. |
| [Standard output](stdout.txt) | The stage boundaries, sample results, and run command. |
| [Standard error](stderr.txt) | The generated trust-boundary warnings. |
