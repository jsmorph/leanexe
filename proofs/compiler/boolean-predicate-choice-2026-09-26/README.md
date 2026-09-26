# Boolean choices containing Boolean-input predicate calls

Candidate `19a6244daf47fc279dba16b560bb5ae276dfe37f` admits Boolean-valued choices whose conditions are
Boolean values or Boolean Eq/Ne relations. Calls may appear in the condition and
either branch, including ordinary and dependent choices. The exact unused proof
binders are preserved. Both branches retain their Boolean checks during compilation;
source evaluation and emitted execution use the selected branch.

- The general source-to-WASM theorem and all eighteen axiom audits pass.
- Native Lean/V8 agree on 575 inputs across 32 selected declarations, including 14 ranges.
- All eighteen shared modules retain identical bytes.
- Focused tests pass 16,052 native/IR comparisons and 11,628 invalid-input checks.
- Prior tests pass 16,660 comparisons and 11,694 invalid-input checks.
- Both test groups include twelve admission controls.
- The full native corpus contains 844 declarations.

[verification.json](verification.json) records commands, source and module hashes.
The [journal](journal.md) records proof work and retained diagnostics. Validation
uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.

Choices over other propositions, direct Boolean contexts and full dialect
compiler correctness remain subsequent work.
