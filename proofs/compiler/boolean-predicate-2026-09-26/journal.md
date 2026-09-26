# Reusable Bool-to-Bool helpers with converted calls

The first increment adds a distinct Boolean-input/Boolean-result lexical function
kind. Its source and compiled matching relations require a Boolean argument and
an encoded Boolean result. Source totality, typed value lookup and compiled
binding lookup pass. The helper body uses the existing independently specified
Boolean expression grammar with its parameter stored as a Boolean value.

Calls initially appear under Bool.toUInt64. The compiler uses the binding's type
to decide whether the raw application takes a Boolean or word argument. The
existing word-predicate parser remains unchanged. Other Boolean-expression calls
require a later typed dispatch extension. Existing word predicates keep their
meaning, and wrong function/value kinds must reject.

The lowering validates helper bodies before creating closures, including unused
helpers. Captures follow the same lexical environment relation as earlier
helpers. Exact arrow/lambda input domains and Boolean result annotations remain
checked. New source rules retain the original declarations and converted calls.

Initial focused diagnostics found omitted exhaustive binding cases in the
mechanical extension and an overbroad generated lookup; both were corrected
before continuing. The new lowering's termination proof had to use the original
parser equality in fallback cases because the inner match introduces a second
parser equality. The equation proofs split dependent matches and use parser
uniqueness instead of rewriting underneath those dependent matches.

The general compiler theorem and all eighteen axiom audits pass. Native Lean/V8
agree on 1,105 inputs across 62 declarations, including 25 ranges. All 51 prior
modules retain identical bytes. The native corpus contains 780 declarations.
New focused tests pass 2,156 comparisons and 2,304 invalid-input checks; prior
word-predicate and Boolean-conversion tests pass 1,466 comparisons and 880
invalid-input checks. The previously rejected converted Boolean helper is now
an admitted fixture, with its conversion suite's comparison count computed and
checked. The raw Boolean-context call fixture remains excluded at this stage.
