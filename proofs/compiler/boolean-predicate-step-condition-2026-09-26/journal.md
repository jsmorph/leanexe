# Direct loop-step Boolean conditions

Reused the scalar Boolean condition compiler for truth tests and Boolean Eq/Ne.
The independent source rules evaluate each actual condition input as a Boolean
conversion and select the native loop step. Scalar environments project out step
functions, preserving the separation between scalar and continuation values.
The old condition path remains for expressions without Bool-input helpers.

Source totality, extraction correctness, acceptance, soundness and invariant
proofs pass. Correctness preserves the accumulator and done flag together. The
first core check exposed do-layout indentation in the new dispatch, corrected by
putting the else expression on its own indented line. Function induction exposed
an attached-list map in dispatch hypotheses; List.attach_map_val normalizes it.
An initial guessed lemma name did not exist. Both diagnostic logs are retained.

The syntax fixture passes 9,216 native/IR comparisons, 5,376 rejection checks and
384 admission controls. The branch/type/evidence fixture passes 360 rejections
and 24 controls, including inactive branches and proof-variable misuse.
The first native fixture requested retained Id wrappers on a Bool parameter,
which remain outside the reusable-helper grammar. The fixture now retains Id
result wrappers with an ordinary Bool input. Broader parameter annotations remain
subsequent work; the failed fixture log records the gap.

All eight native examples agree with the IR on 192 inputs. The first corrected
fixture still carried the preceding suite's 180-count assertion; updated it to
192 without changing any example or expected result. Prior scalar-condition,
loop-let and dependent/local-Boolean fixtures pass 7,892 comparisons, 6,894
rejections and 500 controls.

The general compiler theorem and eighteen axiom audits pass. Native Lean/V8
agree on 521 inputs across 26 declarations, including seventeen ranges. Eighteen
shared modules retain identical bytes. The full native corpus has 890 declarations.
