# Negation around Boolean helper scopes

Candidate `10bbaec9b4c7f81b8cb7b51d8a21e433916a7b3b` admits exact Bool.not applications around recursively
supported Boolean expressions. Negations may repeat and surround direct or
Id-wrapped helper scopes. The source rule uses native Boolean negation, and
lowering reuses the proved zero/one Boolean operation. Scalar conditions,
dependent conditions and loop exits use the same checked conversion.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 993 inputs across 54 declarations, including 25 ranges.
- 44 prior modules retain identical bytes; 0 changed.
- New tests pass 9,588 value/exit comparisons, 8,448 invalid-input checks and 192 controls.
- Prior tests pass 16,692 comparisons, 14,016 invalid-input checks and 384 controls.
- The original negation probe passes unchanged.
- The full native corpus contains 1437 declarations.

[verification.json](verification.json) records commands, source/module hashes and
prior module comparisons. The [journal](journal.md) explains the proof and the
corrected native Id-input probe. Junctions, equality, choices, broader helper
bodies and Id inputs, multiple loops, retained instances, broader signatures and
full-dialect compiler correctness remain open.
