# Monadic scalar bindings in Boolean loop steps

Candidate `859195b9f7d7b42c3978b0e488b1bb5a65291544` admits standard Id word and Boolean bindings inside
Boolean accumulator steps. Exact input and continuation domains, step output
annotations, every retained Id layer and the standard bind instance are checked.
Unused actions are checked. Chained actions preserve lexical captures and
both the Boolean result and the early-exit flag.

- Source totality, extraction and source-to-WASM correctness are proved.
- All nineteen compiler axiom audits pass.
- Native Lean/V8 agree on 1,005 inputs across 52 declarations, including 29 ranges.
- 44 prior modules retain identical bytes; 0 changed.
- New tests pass 14,016 native/IR comparisons and 7,488 invalid-input checks.
- Prior tests pass 30,480 comparisons and 20,736 invalid-input checks.
- Two original probes are restored; two conditional-action probes remain rejected.
- Eight new probes and six prior accumulator probes compile.
- The native corpus contains 1,573 declarations.

[verification.json](verification.json) records commands and source/module hashes.
The [journal](journal.md) records the fixed probes and their remaining limits.
Conditional monadic actions that generate local step-returning continuations,
step-result bindings, other function compositions and full-dialect compiler
correctness remain open.
