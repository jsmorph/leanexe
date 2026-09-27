# Negation around Boolean helper scopes

After the wrapper milestone, valid probes still reject negation, Boolean
junctions, equality, choices, nested helper bodies and Id-annotated helper inputs
in these scalar operand positions. The first Id-input probe attempted a BEq
instance for Id UInt64 and failed native elaboration. That probe was corrected to
compare Id.run n with the captured word; the corrected declaration elaborates
and remains a compiler rejection. The original fixture and both logs are kept.
Negation is the bounded capability selected for this increment.

BooleanNegated preserves the exact Bool.not head and raw operand, with the
syntactic complement of BooleanLocal. Its independent source semantics recursively
evaluates the operand's Boolean conversion and returns the native negated flag.
The parser proves acceptance, soundness, non-overlap and a strict size decrease.
The compiler recursively converts the operand and reuses booleanWordNegation 1;
its established correctness and invariant lemmas apply directly. Recursive
conversion permits arbitrary finite nesting. The existing BooleanScopeGuard and
step proofs carry this to ordinary/dependent conditions and break/continue.

Parser and scalar proofs pass on their first checks. Tests cover one, two and
three negations, direct and Id.run-wrapped helpers, word/Boolean inputs, captures,
unused helpers, nested Id result types, both condition forms, loop exits and final
results. Invalid Bool.not universes, custom heads, word operands, helper bodies,
decisions and proof domains remain rejected. Junctions, equality, choices,
broader helper bodies and Id inputs are kept as separate measured gaps.

New tests pass 9,588 value/exit comparisons, 8,448 invalid-input checks and
192 controls. Six adjacent tests pass 16,692 comparisons, 14,016 invalid-input
checks and 384 controls. Candidate 10bbaec9 passes the complete compiler-proof
build and all nineteen axiom audits (3,367 build targets).

The general compiler proof and nineteen axiom audits pass (3367 build targets). Passed 993 native Lean / independent Wasm engine comparisons across 54 declarations.
44 prior modules retain identical bytes; 0 changed. The full native corpus contains 1437 declarations.
