# Negation around general Boolean scopes

After the inner-wrapper archive is committed, run boolean-helper-composite-probe.lean
unchanged. Select the next rejected capability from actual results. Negation is a
small independent extension if that probe still fails: wrapper support now covers
Id.run/pure/metadata but BooleanLocal still has to recognize the entire operand
of Bool.not.

Use an independent BooleanNegated shape with a raw Boolean body and the syntactic
complement of BooleanLocal, following BooleanWrapped. Accept the exact Bool.not
head with no universe arguments. Add the fallback after the existing helper and
wrapper parsers; old local syntax retains priority. Prove parser acceptance,
soundness, non-overlap and a strict body-size bound. Eliminate the known failed
BooleanLocal test before unfolding wrapper/helper syntax, to preserve Decidable
instances in dependent matches.

The scalar converter recursively compiles Bool.toUInt64(body) and applies
booleanWordNegation 1. Independent source evaluation returns (!flag).toUInt64.
Use booleanWordNegation_correct/holds and the Boolean conversion result lemma
for execution, totality and invariants. Recursive negation admits arbitrary
finite nesting. BooleanScopeGuard and the step proofs should compose unchanged.
Test direct and wrapped helpers, repeated negations, false/true captures, unused
bodies, ordinary/dependent choices, break/continue and final loop results. Invalid
heads, levels, body/value/function kinds, decisions and proof domains remain
rejected. Keep junctions, equality, general Boolean choices, helper bodies and Id
inputs as separate measured gaps until their own end-to-end proofs pass.
