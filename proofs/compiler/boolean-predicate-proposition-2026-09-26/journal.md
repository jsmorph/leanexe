# Boolean-input calls in propositional Boolean choices

The existing ordinary/dependent form now reconstructs propositional choices.
Checked size lemmas cover actual guard operands and converted branch expressions;
no normalized condition is used. Source evaluation requires every guard operand
and only the selected branch. Source support and extraction check both branches.
A typed Boolean-input predicate witness selects the new lowering, preserving the
existing lowering for word-input predicates. Source totality reuses the proved
zero/one conversion result. The shared IR conditional composes existing guard
correctness, selected-branch evaluation and Boolean negation proofs.

The helper scratch, core build and aggregate source/extraction proof passed on
their first runs. The function induction equations were inspected before changing
the soundness cases. Form equations were unfolded explicitly before rewriting.
No new axioms or admissions were introduced.

An initial native example combined a saved Boolean variable with a propositional
comparison in one guard. That form lies outside the current guard grammar, whose
Boolean leaves are closed expressions. The extraction rejection is retained. The
example now tests its captured flag in the selected branch and a supported word
comparison in the guard. Saved Boolean variables in mixed propositional guards
remain on the task list.

New examples cover all six word comparisons, literals, compound propositions,
negation, converted calls in guard operands, ordinary/dependent branches, nested
choices, call arguments, helper bodies, captures, Id blocks, loop bounds,
break/continue and final values. Tests vary binder annotations, Id result depth,
negation depth and dependency flags in scalar/step/outer scopes. Twelve admission
controls and 150 targeted tests check active/inactive branches, proof use, result
types, decision evidence, universes and word/function confusion. Focused totals
are 16,052 native/IR comparisons and 11,670 invalid-input checks. The selected engine
group contains 32 new and relevant prior declarations, including twelve ranges;
eighteen shared modules will be compared with the preceding choice archive.

Prior choice tests pass 16,356 comparisons and 11,640 invalid-input checks, with
twelve admission controls. The general compiler theorem and all eighteen axiom
audits pass. Native Lean/V8 agree on 555 inputs across 32 selected declarations,
including twelve ranges. All eighteen modules shared with the choice archive
retain identical bytes. The full native corpus contains 854 declarations.
