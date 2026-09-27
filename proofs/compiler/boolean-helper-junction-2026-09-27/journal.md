# Conjunctions and disjunctions around Boolean helper scopes

After negation, five valid left/right/both/dependent-condition/loop-exit probes
still fail admission. BooleanJoined records the exact Bool.and or Bool.or head,
raw operands and the syntactic complement of BooleanLocal. Its independent
source rule evaluates both converted operands to encoded Booleans and uses
native conjunction or disjunction. The parser proves acceptance, soundness,
non-overlap and strict size bounds for both children.

Recursive conversion of both children reuses booleanWordJunction 0 and its
existing correctness/invariant lemmas. BooleanScopeGuard carries the extension
to ordinary/dependent scalar conditions and loop-step exits without changing
those proofs. Both operands must be admitted even when a constant determines
the result. Parser, scalar and public proof builds pass on their first checks.

New tests pass 18,996 value/exit comparisons, 18,816 invalid-input checks and
384 controls. They vary operand placement, helper input/result types, captures,
wrappers, negation, unused helpers and break/continue. Invalid universes, custom
heads, malformed helper bodies, evidence and domains remain rejected. Six prior
tests pass 25,460 comparisons, 19,456 invalid-input checks and 704 controls.
The original five probes pass unchanged. The broader composite probe now admits
negation and junctions; equality, choices, nested helper bodies and Id inputs
remain rejected. The selected 54-declaration engine group retains 44 previous
cases and adds ten new cases, with 25 range declarations.

The general compiler proof and nineteen axiom audits pass (3369 build targets). Passed 993 native Lean / independent Wasm engine comparisons across 54 declarations.
44 prior modules retain identical bytes; 0 changed. The full native corpus contains 1447 declarations.
