# UInt64 bindings inside converted Boolean results

Converted UInt64 bindings now check their scalar value and recursively check
their Boolean body when it references a Bool-input predicate. The value keeps a
word binding kind; the body's encoded Boolean is negated as required. Ordinary
lets, immediate applications and named immediate applications retain their exact
input and result annotations. The existing lowering remains for bodies without
Bool-input predicate references.

The independent source rule evaluates the word, then the Boolean body under its
word binding. Totality, correctness, acceptance, soundness and invariants reuse
the scalar evaluator, closure lookup and negation proofs. The binding-size bound
proves both recursive calls decrease under the existing measure. The focused
source/extraction proof passes on its first build.

Dependent loop proof modules and invariants pass. New native/syntax tests pass
7,348 comparisons, 4,608 invalid-input checks and 512 admission controls on the
first run. They cover result annotations, negation, both binder annotations,
ordinary/immediate/named bindings, calls in bound words and Boolean bodies,
captures, shadowing and unused values. Prior tests pass 17,200 comparisons,
10,004 invalid-input checks and 1,024 controls.

The general compiler theorem and eighteen audits pass. Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges. Eighteen shared modules retain identical bytes. The full native corpus has 966 declarations.
