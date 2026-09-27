# General predicate bodies before Boolean-result loops

Candidate `64b4aba8101a8441299106d35029851ee78d4d95` admits nested helpers, wrappers and choices in predicate
bodies declared before Boolean-result loops with UInt64 accumulators. The checked
scalar conversion preserves captures across loop states. Every helper body is
validated, including unused bodies. Existing direct, wrapped and conditional
calls to loop-valued helpers retain their proof paths.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 1,005 inputs across 52 declarations, including 29 ranges.
- 44 prior modules retain identical bytes; 0 changed.
- New tests pass 10,560 comparisons and 3,888 invalid-input checks.
- Prior tests pass 540,144 comparisons, 279,216 invalid-input checks and 15,744 controls.
- Four original probes and eight new declarations pass unchanged.
- The native corpus contains 1545 declarations.

[verification.json](verification.json) records commands, source/module hashes and
prior module comparisons. The [journal](journal.md) records proof and fixture
failures and their corrections. The original probe files retain three rejected
Boolean-accumulator declarations. Four probes of other outer grammars also remain
rejected. Boolean accumulators, those outer grammars, Id inputs in converted
scopes, composition of loops, retained instances, broader signatures and
full-dialect compiler correctness remain open.
