# Standard wrappers around Bool-input predicate calls

BooleanWrapper already describes exact standard pure, Id.run and metadata syntax.
Added an independent source rule that evaluates the converted inner Boolean and
preserves its native wrapper semantics before applying surrounding negation. The
compiler uses this path when the wrapped expression contains a typed Bool-input
helper and preserves the existing BooleanLocal lowering otherwise.

The wrapper's body-size theorem and Boolean negation's size bound justify the
recursive call using scalarExtractionSize. Existing Boolean-word negation lemmas
supply evaluation and invariant preservation. Source totality, acceptance,
soundness and evaluation proofs pass without new axioms or admissions.

The first core check exposed one additional use of the old generic Boolean-word
equation that needed the new wrapper-absence hypothesis. Added the impossible
predicate/wrapper equality case; the aggregate source-to-IR proof then passed.
The syntax fixtures include pure/run/metadata, nested wrappers, two helper/result
annotations, four negation depths, binders, captures and invalid inputs in scalar,
loop-step and outer-loop environments. The initial outer fixture retained an old
960-count assertion; the expanded matrix correctly yields 5,760 checks. An
initial rejection-test parameter used Lean's reserved instance keyword; renamed
it evidence. These diagnostic logs are retained.

Focused tests pass 23,988 native/IR comparisons, 16,716 invalid-input checks and
804 controls. Earlier direct-condition and saved/dependent-Boolean tests pass
15,572 comparisons, 11,598 invalid-input checks and 828 controls. Native examples
include captures, helper arguments, saved flags, direct loop control, bounds and
post-loop results. Boolean do bindings are the next capability; wrapper support
is their prerequisite and does not yet change the bind extractor.

The general compiler theorem and eighteen axiom audits pass. Native Lean/V8
agree on 509 inputs across 28 declarations, including thirteen ranges. Eighteen
shared modules retain identical bytes. The full native corpus has 900 declarations.
