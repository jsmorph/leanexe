# Bounded first-zero removal artifact walkthrough

## Summary

This demo accepts an `Array UInt64`.  An input containing at most eight elements loses its first zero, with the remaining elements kept in order.  A bounded input without a zero returns unchanged, while a longer input returns an empty array.

The compiler produced a 2,183-byte WASM module with SHA-256 digest `7cdd8adba75d4f076d0a142f824a19a0d34d6a5cedd1a810a417a7fc5789f7b6`.  Its exported function has 597 instructions, 23 locals, and five loops.  The artifact theorem proves the specified result directly for those bytes under the pinned Talos semantics, and an independent `leanexegen verify -s` invocation accepted the package.

Demo 12 adds an early-exit search and a variable-length copy-and-shift result to the demonstration set.  The compiler annotated the outer length dispatch but did not annotate either the search or the erase operation.  The proof therefore records both successful transfer from shared LTG material and the remaining need for general first-match and array-erasure proof interfaces.

## Program and specification

The [generation request](request.txt) fixes the public behavior, the length bound, and the required use of `Array.findIdx?` and `Array.eraseIdx!`.  The [formal specification](spec.lean) defines the result, a branch-sensitive heap reserve, the represented-array precondition, and the module property.  The [generated Lean program](program.lean) uses the same bounded search and removal operations.

```lean
def compute (input : Array UInt64) : Array UInt64 :=
  if input.size ≤ 8 then
    match input.findIdx? (fun element => element == (0 : UInt64)) with
    | some index => input.eraseIdx! index
    | none => input
  else
    #[]
```

The [WASM module](program.wasm) is the executable covered by the theorem.  The [WAT rendering](program.wat) exposes the outer length branch, first-match loop, found-index decoding, allocation, prefix-copy loop, shifted-suffix loop, and oversized empty-result path.  The pinned `wasm-tools` 1.251.0 produced the 24,404-byte rendering from the frozen module.

## Artifact proof

The [behavioral proof](proof.lean) begins from a represented input array and the runtime allocation precondition.  The generated length-dispatch recipe splits the execution into bounded and oversized branches without reducing the matched dispatch instructions.  The oversized branch composes the shared capacity, allocator, length-store, finish-program, and empty-array theorems.

The bounded branch relates a machine search index to `Array.findIdx?.loop` and `Array.findIdx?`.  Its invariant proves the exhausted case returns the original represented array and the zero case yields a valid removal index.  The proof then decodes the one-based sentinel, checks the array header and index, applies the shifted allocator theorem, and stores the reduced length.

Two semantic loop invariants describe the removal copy.  The first preserves the prefix before the removed index, while the second copies each later source element one slot toward the front.  `Array.getElem_eraseIdx_of_lt` and `Array.getElem_eraseIdx_of_ge` reconstruct the final `input.eraseIdx! index` representation from those memory facts.

The [compiler annotations](program.proof/program.annotations.json) contain one `leanexe.array.length-dispatch.v1` region.  The [generated annotation equalities](annotation-matches.lean) and [proof recipe](program.proof/proof-recipes.json) establish the exact dispatch match and expose the checked invocation `wp_fixed_array_length_le_dispatch_from hArray at 8, 8`.  No generated annotation summarizes the dynamic first-match search, prefix copy, shifted suffix, or complete erase path.

The [knowledge evaluation](program.proof/knowledge-evaluation.json) records five used LTG entries: allocation, capacity, length dispatch, map-add, and result construction.  The map-add entry supplied a checked indexed-copy invariant pattern rather than a matching whole-function theorem.  The filter entry was rejected because its conditional-store program did not match the search-and-shift artifact.

The [proof journal](program.proof/proof-journal.md) records each retrieval and residual-goal transition.  Exact-size search-chain and search-tree declarations failed to match the dynamic scan, and the catalog contained no applicable `findIdx?` or `eraseIdx!` interface.  The journal identifies two reusable abstractions suggested by the accepted proof: an encoded first-match loop theorem and an in-bounds erase theorem composed from allocation, prefix copy, shifted suffix copy, and array reconstruction.

## Measurement

The [proof telemetry](program.proof/proof-telemetry.json) records 3,907.231311 seconds from the start of Stage 5 to the first accepted proof.  The Codex session used 3,742.213573 seconds, and outer acceptance used 140.403479 seconds.  The accepted proof contains 860 lines, 3,516 whitespace-delimited words, and 39,249 bytes.

The [stage reports](program.proof/stage-reports.json) record one accepted attempt for the formal specification, Lean program, and artifact proof.  The artifact report names both `Behavior.artifact_behavior` and the exact-byte `Artifact.artifact_correct` theorem.  Independent verification checked the complete package after generation and before its byte-for-byte copy into this directory.

## Execution

The first sample removes the first of two zero elements and preserves the second.  The second sample exercises the no-match path, and the third exercises the oversized path.  Direct execution of the proved artifact returned these arrays.

```text
Input: [7, 0, 9, 0]
Output: [7, 9, 0]
Input: [1, 2, 3]
Output: [1, 2, 3]
Input: [1, 2, 3, 4, 5, 6, 7, 8, 9]
Output: []
```

## Retained files

The root files provide readable views of the request, generation result, artifact, and proof.  The [verification package](program.proof/) preserves the embedded artifact, generated proof modules, LTG snapshot, selected guidance, samples, journal, telemetry, tool pins, and manifest accepted by the independent verifier.  Package metadata remains in that directory so the demo does not maintain duplicate JSON views.

| File | Contents |
|---|---|
| [Generation request](request.txt) | The bounded first-zero removal behavior supplied to leanexegen. |
| [Formal specification](spec.lean) | The expected result, runtime precondition, and exact artifact property. |
| [Lean program](program.lean) | The generated source compiled by LeanExe. |
| [WASM module](program.wasm) | The exact executable artifact covered by the proof. |
| [WAT rendering](program.wat) | The textual instruction representation produced by the pinned wasm-tools. |
| [Behavioral proof](proof.lean) | The accepted direct proof of search, removal, and oversized behavior. |
| [Annotation equalities](annotation-matches.lean) | The exact generated length-dispatch program and matching theorems. |
| [Verification package](program.proof/) | The complete package accepted by `leanexegen verify -s`. |
