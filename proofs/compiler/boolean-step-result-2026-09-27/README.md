# Complete Boolean step-result bindings

Candidate `56c76e3a34cc6f3422f6ed19e20ab6552c6fd97d` admits saved Boolean steps, aliases, standard Id binds
and `show` bindings. Results retain both their Boolean value and exit status
through local captures. A done result exits only when returned by the callback;
binding or ignoring it does not exit. Exact result annotations, Id layers,
continuation domains and instances are checked, including unused computations.

- Source totality, extraction and source-to-WASM correctness are proved.
- All nineteen compiler axiom audits pass.
- Native Lean/V8 agree on 1,053 inputs across 54 declarations, including 31 ranges.
- 44 prior modules retain identical bytes; 0 changed.
- New tests pass 18,672 native/IR comparisons and 9,600 invalid-input checks.
- Prior tests pass 65,472 comparisons and 39,456 invalid-input checks.
- Saved, ignored-done and retained/show probes are restored.
- Four prior result/helper probes and six accumulator probes remain accepted.
- A fixed conditional step-result bind still needs a step-argument continuation.
- The native corpus contains 1,593 declarations.

[verification.json](verification.json) records commands and source/module hashes.
The [journal](journal.md) records the proved binding behavior and fixed probes.
Functions taking complete Boolean steps, step-result pattern matching and
full-dialect compiler correctness remain open.
