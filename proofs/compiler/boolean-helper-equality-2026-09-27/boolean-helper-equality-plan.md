# Equality and inequality around Boolean helper scopes

The unchanged composite equality probe remains rejected after junction support.
Extend conversion with exact standard Boolean equality/inequality and decisions
of Boolean Eq/Ne. Preserve the actual head, universe, default BEq instance,
relation and decision evidence. A raw relation syntax type keeps both operands
independent of BooleanLocal; a complementary source shape ensures parser priority.

The independent source evaluation recursively evaluates both converted operands
and uses BooleanEqualityForm.denote. Prove parser acceptance, soundness and both
size bounds, plus non-overlap with preceding helper/wrapper/negation/junction
forms. Reuse booleanWordEquality 0 and its correctness/invariant theorems. Both
operands are checked; reflexivity does not admit an unsupported operand.

Tests cover helpers on either and both sides, native BEq/bne and decide Eq/Ne,
wrappers, negation, dependent conditions, loop steps/exits and final results.
Reject alternate instances/evidence, heads, universes, domains and wrong operand
types. Retain the existing fixture and adjacent junction/equality cases, finish
the source-to-WASM and independent engine gates, then proceed to choices.
