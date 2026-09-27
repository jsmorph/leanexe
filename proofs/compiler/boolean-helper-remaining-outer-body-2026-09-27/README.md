# General predicate bodies around word-result loop compositions

Candidate `39c65d57325d19c96d76c9f86a559c614451b091` admits nested helpers, wrappers and choices in predicate
bodies surrounding Boolean-derived word results and word-valued conditionals.
Both helper input kinds preserve lexical captures. Every helper body is checked,
including unused bodies and bodies in unselected branches.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 1,005 inputs across 52 declarations, including 29 ranges.
- 44 prior modules retain identical bytes; 0 changed.
- New tests pass 20,928 comparisons and 7,776 invalid-input checks.
- Prior tests pass 139,584 comparisons, 77,616 invalid-input checks and 9,216 controls.
- Four original probes and eight new declarations pass unchanged.
- Four earlier general-body probes still pass; their Id-input probe remains rejected.
- The native corpus contains 1553 declarations.

[verification.json](verification.json) records commands, source/module hashes and
prior module comparisons. The [journal](journal.md) records the separate focused
proof builds and tests. Boolean accumulators, Id inputs in converted helper
scopes, composition of loops, retained instances, broader signatures and
full-dialect compiler correctness remain open.
