# Local predicate bindings inside propositions

Candidate `768f4ea1963c8a50e5cd6e28468ab82522ecacc2` admits UInt64-to-Bool and Bool-to-Bool function lets
inside supported propositions. Original function annotations, captures and
substituted standard decision evidence are preserved. Every helper body is
validated, including unused bodies. All existing termination bounds remain
proved with the checked syntax allowance for the validation operand.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 993 inputs across 54 declarations, including 25 ranges.
- 44 prior modules retain identical bytes; 0 changed.
- New tests pass 72,756 comparisons, 75,568 invalid-input checks and 576 controls.
- Prior tests pass 118,452 comparisons, 106,392 invalid-input checks and 1,920 controls.
- The original compound probe passes unchanged, as do seven prior controls.
- The full native corpus contains 1497 declarations.

[verification.json](verification.json) records commands, source/module hashes and
prior module comparisons. The [journal](journal.md) records the size measurements,
proof checks and split public dependency build after its initial time limit.
Nested helper bodies, Id inputs, composition of loops, retained instances, broader
signatures and full-dialect compiler correctness remain open. The next probe and
its admission results are retained for the following capability.
