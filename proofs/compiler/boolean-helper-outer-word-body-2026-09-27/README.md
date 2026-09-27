# General predicate bodies before word-result loops

Candidate `4e3205301c5be854c1711645544b0b726f5c274b` admits nested helpers, wrappers and choices in predicate
bodies declared before UInt64-result loops. The checked scalar conversion
preserves captures across loop states. Every body is validated, including unused
bodies. Helpers may supply bounds, initial values, loop steps and final results.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 1,053 inputs across 54 declarations, including 31 ranges.
- 44 prior modules retain identical bytes; 0 changed.
- New tests pass 10,608 comparisons and 3,888 invalid-input checks.
- Prior tests pass 41,136 comparisons, 25,056 invalid-input checks and 1,152 controls.
- Ten new probes and the original two outer-prefix probes pass unchanged.
- Four prior step controls still pass.
- The full native corpus contains 1537 declarations.

[verification.json](verification.json) records commands, source/module hashes and
prior module comparisons. The [journal](journal.md) records the raw-body prefix
proofs and unused-helper checks. Five Boolean-result loop probes remain rejected
and are retained for the next capability. Their helper dispatcher, other outer
grammars, Id inputs in converted scopes, composition of loops, retained instances,
broader signatures and full-dialect compiler correctness remain open.
