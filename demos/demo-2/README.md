# Bounded Association-List Artifact Walkthrough

## Summary

This demo asks `leanexegen` to generate an `Array UInt64 → Array UInt64` program for a bounded association-list lookup.  A well-formed input contains a query followed by ten key-value pairs.  The program returns the value from the first matching pair and a found flag, or returns two zeroes when no key matches or the input has the wrong length.

`leanexegen` generated the formal specification and Lean source, compiled the source to a 7,336-byte WASM module, and proved the behavior of those exact WASM bytes in Lean.  The artifact proof does not use the generated source or a compiler-correctness theorem.  Lean accepted both the behavioral theorem for the Talos module and the final theorem for the embedded WASM artifact.

The direct artifact-proof stage took 54 minutes 21 seconds.  Codex used 53 minutes 5 seconds to construct and revise the proof, while the outer acceptance checks used 68 seconds.  The result provides the baseline for reducing proof-generation time on fixed-size input scans and two-element array results.

## Request and interface

The [generation request](request.txt) fixes a 21-word input representation.  Element zero is the query, and the remaining twenty elements form ten key-value pairs.  The search proceeds from left to right, so repeated keys return the value associated with the first occurrence.

```text
[query, key1, value1, key2, value2, ..., key10, value10]
```

The [formal specification](spec.lean) defines `expected` with an exact length check followed by ten ordered comparisons.  It also defines the array representation in WASM memory, the required initial runtime state, and the public `ArtifactSpec`.  The [generated Lean program](program.lean) implements the same total function using the requested public type.

## Compiled artifact and proof

The retained [WASM module](program.wasm) has SHA-256 digest `ceb37cd3d61158e7f4162c97cac9b79022518a4e67f895d45a3619c7b5a29712`.  The [WAT rendering](program.wat) exposes the complete instruction sequence used to generate the Talos program model.  The WASM bytes remained fixed throughout direct artifact-proof generation.

The [behavioral proof](proof.lean) contains 1,639 lines.  It proves the generated decision tree from memory reads, handles allocation and construction of the two-word result array, and establishes the public theorem for every input satisfying the runtime representation predicate.  The proof imports general array, allocation, and control-flow support, but it still contains an artifact-local allocator theorem because the current reusable allocator theorem fixes its local-variable indices.

Lean accepted the final proof twice after Codex's last edit.  The accepted behavioral theorem is `Behavior.artifact_behavior`, and the package's deterministic artifact modules derive `Artifact.artifact_correct` for the embedded bytes.  The [stage report](stage-reports.json) records both accepted declarations and the generated-task reports.

## Execution and timing

The retained run uses a query that occurs twice.  The first matching key has value `20`, so the later value `30` does not affect the result.  The generated WASM returned the expected pair.

```text
Input: [42, 1, 10, 42, 20, 42, 30, 4, 40, 5, 50, 6, 60, 7, 70, 8, 80, 9, 90, 10, 100]
Output: [20, 1]
```

The [captured standard output](stdout.txt) records every stage boundary, the sample result, and the executable command.  The [captured standard error](stderr.txt) records the four trust-boundary warnings emitted after publication.  The [proof telemetry](proof-telemetry.json) supplies the machine-readable start time, acceptance time, Codex duration, outer-check duration, total duration, and accepted proof digest.

## Retained files

| File | Contents |
|------|----------|
| [Generation request](request.txt) | The bounded association-list behavior supplied to `leanexegen`. |
| [Formal specification](spec.lean) | The generated mathematical function and artifact-level specification. |
| [Lean program](program.lean) | The generated source program compiled by LeanExe. |
| [WASM module](program.wasm) | The exact executable artifact covered by the proof. |
| [WAT rendering](program.wat) | The textual rendering used to construct the Talos program model. |
| [Behavioral proof](proof.lean) | The accepted direct proof of the generated WASM behavior. |
| [Proof telemetry](proof-telemetry.json) | The measured stage-five proof-generation and acceptance times. |
| [Stage reports](stage-reports.json) | The accepted reports for specification, source, and artifact-proof generation. |
| [Standard output](stdout.txt) | The complete user-facing stage and sample output. |
| [Standard error](stderr.txt) | The generated trust-boundary warnings. |
