# Scalar helpers within Boolean loop steps

Candidate `b47aa7c75fee4dc142297bc6200379e0b314e015` admits all four word/Boolean input/output combinations
for local scalar helpers inside Boolean steps. Exact standard Id annotations,
captures, nested/repeated calls and unused bodies are checked. Existing scalar
closure semantics and WASM representations are reused.

- Source totality, extraction and source-to-WASM correctness are proved.
- All nineteen compiler axiom audits pass.
- Native Lean/V8 agree on 1,101 inputs across 56 declarations, including 33 ranges.
- 44 prior modules retain identical bytes; 0 changed.
- New tests pass 27,936 native/IR comparisons and 16,128 invalid-input checks.
- Prior tests pass 81,840 comparisons and 43,296 invalid-input checks.
- Four fixed scalar-helper probes are restored; four result-function probes remain accepted.
- The native corpus contains 1,615 declarations.

[verification.json](verification.json) records commands and source/module hashes.
The [journal](journal.md) records proof adjustments and unchanged probes.
Step-result pattern matching and full-dialect compiler correctness remain open.
