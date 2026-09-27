# Local functions returning Boolean loop steps

The prior increment preserves two rejected conditional-action probes. Their
explicit elaboration contains local functions returning ForInStep Bool. A
separate binding/value layer now distinguishes scalar bindings from word and
Boolean step-returning closures, including lexical matches for both compiled
projections and source/target typed lookup. The first foundation build needed
explicit types on the quantified matching binders. The corrected build passes
(20 targets). The source step grammar migrates to projected scalar contexts and
its totality proof passes (66 targets). Step extraction proofs then needed the
updated constructor binder order in the conditional evaluation case. Corrected
extraction proofs pass (147 targets). Range entry points are being connected
before function declarations and calls are enabled.

The range integration needed explicit congruence for mapping scalar binding
kinds into the new context; simplification alone unfolded the kind function
before it could use the original typing equality. Matching scalar contexts are
embedded by the shared ofScalar lemma. Distinct membership names avoid
shadowing the map-membership premise. All range proofs now pass (180 targets).

Public extraction passes (205 targets). Both existing Boolean syntax suites
pass after the context migration: 27,648 comparisons and 14,400 invalid-input
checks. Four new fixed helper probes all remain rejected before enabling calls.

Source totality for function declarations and calls passes first try. A checked
induction diagnostic records sixteen extractor cases. The first combined
extraction proof needed the full equation for ordinary lets: specialized
equation rewriting could not reduce their abstract type annotations after
adding function patterns. Boolean-call Option lookup hypotheses had already
been expanded by simplification and needed reconstruction where an equality
was expected. Corrected acceptance, support, correctness and invariants all
pass (147 targets). Only standard kernel-checked proof steps are used.

Public extraction passes again (205 targets). Both original conditional-action
probes and both new variants now compile unchanged; ten earlier positive bind
controls remain accepted. Three new helper probes pass; the retained/show probe
still contains a complete step-result binding and remains rejected for the next
capability. Syntax tests pass 20,736 comparisons and 11,232 invalid-input checks
on their first run. The native test first needed an explicit Bool type on a
word-tail loop result; inference retained Id Bool where the conditional expected
Bool. The failed file/log are preserved. Explicit helper function annotations
exercise retained Id domains/results without the separate show binding. The
corrected ten native programs pass 240 comparisons.
