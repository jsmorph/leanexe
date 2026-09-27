# General Boolean bodies in converted local helpers

Candidate `d44def85182b4347826483b7a25289ea14199b99` admits nested predicate declarations, wrappers and
choices in local helper bodies within Boolean conversions. Both body and
continuation are recursively checked, preserving exact helper syntax, captures
and Boolean result encoding. Unused helper bodies are still validated.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 993 inputs across 54 declarations, including 25 ranges.
- 44 prior modules retain identical bytes; 0 changed.
- New tests pass 37,812 comparisons, 33,792 invalid-input checks and 768 controls.
- Prior tests pass 76,252 comparisons, 77,744 invalid-input checks and 640 controls.
- Three original probes pass unchanged; two separate unsupported forms remain recorded.
- The full native corpus contains 1507 declarations.

[verification.json](verification.json) records commands, source/module hashes and
prior module comparisons. The [journal](journal.md) explains why existing
recursive body proofs apply to the raw syntax. Ordinary word-continuation helper
bodies, Id inputs, composition of loops, retained instances, broader signatures
and full-dialect compiler correctness remain open.
