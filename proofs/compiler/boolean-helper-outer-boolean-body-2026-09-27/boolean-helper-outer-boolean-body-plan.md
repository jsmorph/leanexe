# General predicate bodies before Boolean-result loops — possible next capability

Measure the fixed Boolean-result probes after the word-result RangeExit prefix
is completed. They cover word and Boolean predicate inputs, word and Boolean
accumulators, an Id body/result and an unused predicate. Do not infer rejection
without running them: the public dispatcher may already reuse a supported path.

If they remain rejected, scalarBooleanRangePredicate is the likely restriction.
It parses BooleanLocal before checking the scalar Bool.toUInt64 conversion.
booleanRangePredicate also stores BooleanLocal. Generalize these two helpers to
raw expressions and adjust scalarBooleanRangeContinuation_success and
_accepts_scalar accordingly, keeping the scalar-first/direct-call fallback order.
The source BooleanRange letPredicateFn/letBooleanPredicateFn rules already have
scalar conversion premises and can retain raw bodies. Preserve the separate
loop-valued helper, wrapped call and conditional continuation paths.

The success lemma's first alternative need only supply the checked conversion
of the exact raw value and the resulting typed closure, instead of a parsed
BooleanLocal plus value-equality witness. Update its consumers, BooleanRange
source totality, equations, acceptance, correctness, support and invariants. Keep
all standard evidence and syntax checks in the other continuation alternatives.
The dedicated BooleanWordRange and WordRange prefixes are still separate until
fixed probes show whether additional work is needed.
