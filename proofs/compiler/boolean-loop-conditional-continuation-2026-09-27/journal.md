# Conditional calls to local Boolean loop functions

The conditional parser removes the helper binder from the condition/evidence
only when neither refers to the helper. Branches retain their helper references.
It preserves the exact Boolean output type and proves both arm-size bounds.
Independent source rules select one helper-let branch using the captured decision;
source support checks both branch programs.

A lazy complete-continuation helper tries existing scalar/direct/forwarded call
extraction first, then the conditional fallback. Each branch reuses the original
helper declaration with a smaller enclosing body. The existing plan.choice
correctness and invariant lemmas combine the selected plans; WASM lowering is
unchanged. The callback's arm-size proof makes recursion explicit.

The source parser and size proofs pass on their first build. Source evaluation
needed an explicit Bool.toUInt64 annotation for its decision flag. The standalone
continuation helper's acceptance proof needed an explicit split of its dependent
parser match. Extraction acceptance then needed explicit callbacks when applying
the old direct-call acceptance lemma. Source support recovery, correctness and
invariant proofs pass, as do public extraction and WASM admission.

Ten native fixtures include the previously saved conditional-do failure, word
and Boolean arguments, captured predicates, nested conditions, break/continue,
stride and retained Id annotations. Raw syntax checks will compare both public
and direct range extraction with equivalent ordinary argument bindings, and
reject helper capture in conditions/evidence, incorrect conditional syntax and
invalid branches.

All ten native fixtures pass on their first run, including the exact saved
conditional-do computation under a unique declaration name. Raw tests pass
96,768 native/IR comparisons across public extraction, direct range extraction
and equivalent ordinary argument bindings, with 46,080 invalid-input checks and
2,304 binding controls. They cover nested conditions, both input kinds, retained
Id annotations, all binder forms, wrapper/no-wrapper forwarding, scalar/mixed/loop
helper bodies and both public parameter orders. Invalid branches are checked even
under constant decisions; conditions/evidence cannot capture the helper binder.

The complete compiler proof and nineteen axiom audits pass. Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1276 declarations.
