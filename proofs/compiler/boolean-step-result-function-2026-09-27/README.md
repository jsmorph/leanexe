# Functions taking complete Boolean step results

Candidate `927a33b3f312a7bea3b8c8e97d6981807ffdb71f` admits local functions taking and returning complete
Boolean loop-step results. Nested/repeated calls, captures, standard Id layers
and conditional monadic continuations preserve both the value and exit status.
An ignored done argument does not stop the loop. Function bodies and call
arguments are checked even when unused or inside an empty range.

- Source totality, extraction and source-to-WASM correctness are proved.
- All nineteen compiler axiom audits pass.
- Native Lean/V8 agree on 1,053 inputs across 54 declarations, including 31 ranges.
- 44 prior modules retain identical bytes; 0 changed.
- New tests pass 14,064 native/IR comparisons and 8,064 invalid-input checks.
- Prior tests pass 67,776 comparisons and 35,232 invalid-input checks.
- Four fixed function probes and the conditional result bind are restored.
- Three prior result probes remain accepted.
- The native corpus contains 1,603 declarations.

[verification.json](verification.json) records commands and source/module hashes.
The [journal](journal.md) records the proof adjustment and unchanged probes.
Scalar helper declarations within Boolean steps, step-result pattern matching
and full-dialect compiler correctness remain open.
