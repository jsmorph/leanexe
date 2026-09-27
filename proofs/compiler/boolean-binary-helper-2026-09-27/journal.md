# Two-argument UInt64-to-Bool local helpers

All six fixed native probes reject. The initial source syntax retains the two
UInt64 type/lambda parameters, Boolean result annotation, declaration name and
nondep flag. Exact declaration and call recognizers, reconstruction, complete
admission and size bounds pass 87 targets on the first attempt.

A distinct binary predicate kind is added to source values and compile-time
bindings. Its matching relation preserves both arguments and encodes the native
Bool result. Lookup, kind, totality and invariant properties are proved. The
first generated edit duplicated the new lookup declarations at two namespace
end markers; the duplicate was removed. Binding proofs then pass 11 targets.

Existing scalar integration exposed one exhaustive word-binding case. Replacing
that case enumeration with the existing word-projection theorem proves the same
fact for every binding kind. Scalar expression evaluation, acceptance, source
reconstruction and invariants pass with the new kind. Binary helper/call exclusion
proofs also pass. The call exclusion needs the parser equation and comparison
parser unfolded; it is not definitionally reduced by rfl alone. All failures and
corrections are preserved in the focused logs.

This foundation does not yet admit binary predicates. Source evaluation/support,
compiler dispatch and their general proofs are the next steps.

Source evaluation and support now cover converted binary calls, ordinary scalar
helper lets and helper lets within Boolean scopes. Totality passes 63 targets.
The result-encoding proof needed the exact helper renderer unfolded to rule out
an ordinary let at a Bool.toUInt64 head.

The production extractor adds exact binary predicate dispatch after existing
paths reject. Its termination proof initially simplified the full parser context;
simplifying only the size bounds closes all three outer-helper obligations.
Core extraction passes 141 targets. The new extraction equations are in a small
separate module. The many-function exclusion uses the zero arity of a terminal
result; unfolding that arity completes the equation proof (142 targets).

The generated functional induction theorem has 106 cases: the new outer helper
is case 47, converted call case 65, converted helper case 67, and final converted
rejection case 66. Reconstruction follows those exact cases. Evaluation
correctness, complete acceptance, reconstruction and generic IR invariants pass
143 targets on their first combined run. Five new audits cover native binary
application and both directions of the declaration/call recognizers. Loop and
function integration, native tests, full WASM proofs and V8 checks remain.

Loop integration exposed one exact-literal inversion in ScalarRangeCount. Its
impossible let-helper case closes after unfolding the helper renderer. The same
renderer is included in the two related literal/head evaluation proofs. Bounded
integration then passes 198 targets through Boolean word ranges and 210 through
functions. All six fixed probes compile. Eleven native fixtures pass 194
comparisons, including an asymmetric argument-order case. The independent syntax
matrix passes 16128 comparisons, 27072 invalid-input checks and 288 admission
controls first try. It distinguishes predicate and word function kinds, rejects
wrong arities/domains, checks unused bodies and both arguments, and covers ordinary
and converted helper scopes, result annotations and conditional consumers.

The complete source-to-WASM gate passes 3396 targets and all 38 audits. Passed 1403 native Lean / independent Wasm engine comparisons across 74 declarations.
63 prior modules retain identical bytes; 0 changed. All six fixed binary helper probes compile. Prior tests pass 32756 comparisons, 52995 invalid-input checks and 768 admission controls. Five fixed loop-step binary-helper probes compile; the early-exit probe rejects and defines the next increment.
