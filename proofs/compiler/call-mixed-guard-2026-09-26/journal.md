# Boolean helper calls in mixed propositional guards

A mixed Boolean guard leaf may retain a direct local helper application and its
argument. The operand remains a checked Bool.toUInt64 conversion. The existing
typed call extractor distinguishes Bool and UInt64 inputs, rejects functions used
as values or values used as functions, and preserves captured environments.
Boolean and propositional negation keep their exact source syntax. The parser's
round-trip and disjointness proofs extend to the application form. The existing
guard lowering needs no changes.

Parser, scalar extraction, loop extraction and both IR invariant builds pass on
their first invocation. The previous saved-variable syntax fixture supplies the
new explicit absent-argument field; its expectations and counts are unchanged.
Native tests pass 180 comparisons across six scalar and four range declarations.
Syntax tests pass 17,920 comparisons, 12,288 invalid-input checks and 256 controls.
They cover both input types, nested Boolean calls, retained Id result annotations,
ordinary/dependent choices and decisions, captures, negation, changed decision
arguments, wrong argument types, missing names and nonfunction bindings.
All tests pass on their first invocation. Prior checks pass 28,428 comparisons,
18,633 invalid-input checks and 768 controls.

The general compiler theorem and eighteen audits pass. Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges. Eighteen shared modules retain identical bytes. The full native corpus has 996 declarations.
