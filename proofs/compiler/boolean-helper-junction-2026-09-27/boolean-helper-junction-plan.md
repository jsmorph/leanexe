# Boolean conjunctions and disjunctions around helper scopes

After the negation evidence is committed, rerun the existing composite probe.
Negation should pass; conjunction, equality, choices, helper bodies and Id inputs
remain rejected. Add an independent BooleanJoined shape (Junction, raw left and
right operands, syntactic complement of BooleanLocal). Its syntax is the exact
Bool.and/Bool.or head. Parse after the helper, wrapper and negation fallbacks,
keeping the existing grammar's priority.

Recursively convert both operands under the same bindings, then lower with
booleanWordJunction 0. Source evaluation uses Junction.denote, which is defined
using native Bool operators. Source totality obtains each operand's zero/one
Boolean conversion result. Existing booleanWordJunction_correct/holds supply
execution and IR invariants; BooleanScopeGuard and step conditions should require
no changes. Both sides are checked even when one determines the Boolean result.

Prove each child's strict size bound, parser accepts/soundness and non-overlap.
Tests should cover helpers on either side and both sides, word/Boolean inputs,
negation, wrappers, captures, inactive unsupported operands, result annotations,
ordinary/dependent choices, break/continue and loop results. Preserve the original
conjunction fixture. Finish source-to-WASM proof and independent engine checks
before proceeding to equality or choices.
