# Inner Boolean helper scopes

Candidate `a9c412fd6f1866af749c8e7431a9ce758dc4ad37` admits local UInt64-to-Bool and Bool-to-Bool helpers
inside Boolean-to-word conversions and direct conditions. Repeated calls,
captures, nested scopes, Id result annotations and unused bodies are checked.
Ordinary and dependent conditions validate decision expressions and proof domains.
The step proof preserves both the accumulator and the break/continue decision.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Passed 993 native Lean / independent Wasm engine comparisons across 54 declarations.
- 40 prior modules retain identical bytes; 4 changed.
- Focused tests pass 3,316 value/exit comparisons, 2,176 invalid-input checks and 64 controls.
- Prior tests pass 123,360 comparisons, 78,424 invalid-input checks and 4,448 controls.
- The full native corpus contains 1417 declarations.

Some public helper bodies now use the existing scalar fast path instead of a
zero-iteration range plan. The tests compare native, public and explicit range
execution, including unused-helper controls. The original plan-identity test
and its failure are retained.

[verification.json](verification.json) records source/module hashes and prior
module comparisons. The [journal](journal.md) explains proof changes and retained
failures. General Id.run/pure wrappers around helper scopes, multiple loops,
retained instances, broader signatures and full-dialect compiler correctness
remain open.
