# Bounded Binary-Tree Artifact Walkthrough

## Summary

This demo asks `leanexegen` to generate an `Array UInt64 → Array UInt64` program for lookup in a fixed seven-node binary tree.  A well-formed input contains a query followed by seven key-value nodes in breadth-first order.  The program follows equality and unsigned less-than branches from the root to one leaf, returning `[value, 1]` for a visited match and `[0, 0]` when the path misses or the input has the wrong length.

`leanexegen` generated the formal specification and Lean source, compiled the source to a 7,186-byte WASM module, and proved the behavior of those exact WASM bytes in Lean.  The artifact-proof task received the formal specification and WAT-derived Talos program, but it did not receive the generated source or a compiler-correctness theorem.  Lean accepted `Behavior.artifact_behavior` and the final embedded-byte theorem `Artifact.artifact_correct`.

The direct artifact-proof stage took 40 minutes 27.376 seconds.  Codex used 38 minutes 53.467 seconds inside its Lean-driven session, and the independent outer acceptance used 1 minute 23.490 seconds.  The accepted proof uses the shared shifted-allocator and fixed-result modules, while its remaining 1,398 lines expose the cost of proving the artifact's nested comparison tree.

## Request and interface

The [generation request](request.txt) fixes a 15-word input representation.  Element zero is the query, elements one and two hold the root, and each later key-value pair follows breadth-first tree order.  The traversal defines total behavior for every 15-word array without assuming or validating that its keys satisfy a binary-search-tree ordering.

```text
[query,
 rootKey, rootValue,
 leftKey, leftValue, rightKey, rightValue,
 leftLeftKey, leftLeftValue, leftRightKey, leftRightValue,
 rightLeftKey, rightLeftValue, rightRightKey, rightRightValue]
```

The [formal specification](spec.lean) defines `expected` through a length check and a three-level decision tree.  The [generated Lean program](program.lean) implements the same total function with the requested public type.  Both generated tasks passed their prescribed Lean checks, and the source task also passed the LeanExe acceptance report and WASM compilation.

## Compiled artifact and proof

The retained [WASM module](program.wasm) has SHA-256 digest `1a93ec55974666ad54fad73d321b8b9e1f7d67970b272c13bcc77055c8e7631d`.  The [WAT rendering](program.wat) contains the complete textual instruction form used to construct the Talos program model.  The WASM bytes remained frozen throughout direct artifact-proof generation and the independent final check.

The [behavioral proof](proof.lean) imports `Project.ProofKit.FixedArrayAllocatorWindow` and applies its allocator theorem with offset ten.  It also uses `Project.ProofKit.FixedArrayResult.lengthStore_spec`, `payloadStore_spec`, and `pairStore_at` for the two-element outputs.  Application-specific proof text establishes indexed input reads, comparison branches, and the equation between each reached leaf or match and `FormalSpec.expected`.

The accepted proof has 1,398 lines and 66,527 bytes.  Its shared helpers prove constant and input-derived result construction once, then the public theorem composes those helpers across the exact artifact tree.  The [stage report](stage-reports.json) records the accepted specification, source, and artifact-proof declarations, while the [proof telemetry](proof-telemetry.json) records the stage-five timing and accepted source digest.

## Execution and retained files

The retained sample searches a valid binary-search tree for key 12.  The traversal moves from root key 10 to right child key 15, then to left leaf key 12, whose value is 120.  The compiled artifact returned the expected found pair.

```text
Input: [12, 10, 100, 5, 50, 15, 150, 3, 30, 7, 70, 12, 120, 18, 180]
Output: [120, 1]
```

The [captured standard output](stdout.txt) records the stage boundaries, sample result, and executable command.  The [captured standard error](stderr.txt) records the four trust-boundary warnings emitted after publication.  Every retained file has a distinct role in reproducing, inspecting, or timing the demo.

| File | Contents |
|---|---|
| [Generation request](request.txt) | The fixed seven-node tree behavior supplied to `leanexegen`. |
| [Formal specification](spec.lean) | The generated mathematical function and artifact-level specification. |
| [Lean program](program.lean) | The generated source program compiled by LeanExe. |
| [WASM module](program.wasm) | The exact executable artifact covered by the proof. |
| [WAT rendering](program.wat) | The textual WebAssembly representation used for the Talos model. |
| [Behavioral proof](proof.lean) | The accepted direct proof of the generated WASM behavior. |
| [Proof telemetry](proof-telemetry.json) | The measured proof-session and outer-acceptance intervals. |
| [Stage reports](stage-reports.json) | The accepted reports for all three generated tasks. |
| [Standard output](stdout.txt) | The complete user-facing stage and sample output. |
| [Standard error](stderr.txt) | The generated trust-boundary warnings. |
