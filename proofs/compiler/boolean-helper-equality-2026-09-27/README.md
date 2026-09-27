# Equality and inequality around Boolean helper scopes

Candidate `2ec506c5ba7828c2c7276be07b07e9693a00d636` admits standard Boolean equality/inequality and decisions
of Boolean Eq/Ne around recursively supported operands. Helpers may occur on
either or both sides, with wrappers and negation. The exact comparison instance,
relation and decision evidence are checked. Source evaluation uses native Boolean
relations and lowering reuses the proved zero/one comparison. Scalar conditions,
dependent conditions and loop exits use the same checked conversion.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 993 inputs across 54 declarations, including 25 ranges.
- 44 prior modules retain identical bytes; 0 changed.
- New tests pass 37,812 comparisons, 45,312 invalid-input checks and 768 controls.
- Prior tests pass 34,868 comparisons, 29,824 invalid-input checks and 896 controls.
- Ten original probes pass unchanged.
- The full native corpus contains 1457 declarations.

[verification.json](verification.json) records commands, source/module hashes and
prior module comparisons. The [journal](journal.md) explains the proof. Choices,
broader helper bodies and Id inputs, multiple loops, retained instances, broader
signatures and full-dialect compiler correctness remain open.
