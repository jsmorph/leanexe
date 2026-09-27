# Conjunctions and disjunctions around Boolean helper scopes

Candidate `4d9d4445629c23f6a81ae6f6d10e0c8ea59fd54a` admits exact Bool.and and Bool.or applications around
recursively supported Boolean expressions. Helpers may occur on either or both
sides, with wrappers and negation. Both operands must be supported. Source
evaluation uses native Boolean operations and lowering reuses the proved
zero/one operations. Scalar conditions, dependent conditions and loop exits
use the same checked conversion.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 993 inputs across 54 declarations, including 25 ranges.
- 44 prior modules retain identical bytes; 0 changed.
- New tests pass 18,996 comparisons, 18,816 invalid-input checks and 384 controls.
- Prior tests pass 25,460 comparisons, 19,456 invalid-input checks and 704 controls.
- Five original probes pass unchanged.
- The full native corpus contains 1447 declarations.

[verification.json](verification.json) records commands, source/module hashes and
prior module comparisons. The [journal](journal.md) explains the proof. Equality,
choices, broader helper bodies and Id inputs, multiple loops, retained instances,
broader signatures and full-dialect compiler correctness remain open.
