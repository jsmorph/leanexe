# Local functions returning Boolean loop steps

Candidate `a21f5790293aa63ce829e25448392e834f3812dd` admits word- and Boolean-argument local functions
returning Boolean loop steps. Functions preserve captures and both value and
exit status. Exact input domains and step output annotations may retain Id
layers. Unused bodies and all call arguments are checked. Conditional monadic
actions use the same proved local continuation rules.

- Source totality, extraction and source-to-WASM correctness are proved.
- All nineteen compiler axiom audits pass.
- Native Lean/V8 agree on 1,053 inputs across 54 declarations, including 31 ranges.
- 44 prior modules retain identical bytes; 0 changed.
- New tests pass 20,976 native/IR comparisons and 11,232 invalid-input checks.
- Prior tests pass 44,496 comparisons and 28,224 invalid-input checks.
- Four fixed conditional-action probes and three helper probes are restored.
- Ten prior bind probes and six accumulator probes remain accepted.
- A fixed `show` probe still needs complete step-result bindings.
- The native corpus contains 1,583 declarations.

[verification.json](verification.json) records commands and source/module hashes.
The [journal](journal.md) records source context changes, proof diagnostics,
fixed probes and the remaining step-result limitation. Complete Boolean step
bindings, functions taking step results and full-dialect compiler correctness
remain open.
