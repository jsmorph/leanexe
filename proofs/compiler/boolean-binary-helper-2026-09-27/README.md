# Two-argument UInt64-to-Bool local helpers

Candidate `633e9d6ee97d19b2db57df0c07ad72484570ebef` admits binary Boolean helpers in scalar bodies and
Boolean expression scopes, including scalar computations within loop steps and
post-loop results. Both input domains must be UInt64; results may retain standard
Id layers. A distinct function kind preserves Boolean results and argument order.
Captured values, repeated calls, nested unary helpers and unused bodies are checked.

- Source, extraction and source-to-WASM correctness are proved; all 38 audits pass.
- The native binary application equation has no axioms.
- Native Lean/V8 agree on 1,403 inputs across 74 declarations, including 38 ranges.
- 63 prior modules retain identical bytes; 0 changed.
- New tests pass 16,322 native/IR comparisons, 27,072 invalid-input checks and 288 admission controls.
- Prior tests pass 32,756 comparisons, 52,995 invalid-input checks and 768 admission controls.
- All six fixed binary-helper probes compile.
- The native corpus contains 1,683 declarations.

[verification.json](verification.json) records commands and source/module hashes.
The [journal](journal.md) preserves failed proof attempts and corrections.
Binary predicate declarations in loop-step bodies and full-dialect correctness
remain open.
