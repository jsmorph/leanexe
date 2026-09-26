# Boolean-input predicates declared before loops

The outer range source grammar now admits reusable Bool-to-Bool helper
declarations with explicitly converted calls. The source rule retains exact
Boolean parameter domains and Boolean/Id result annotations. Scalar closure
values capture the original lexical environment. Source totality and the proof
excluding loop-containing expressions from pure scalar extraction pass.

The range extractor's existing Bool-input, word-result declaration path now has
a checked Boolean-result alternative. It validates the Boolean body before
adding its closure, including unused declarations. The source acceptance,
soundness, evaluation and IR invariant proofs passed their first focused run.
The evaluation proof matches each closure for every accumulator, index, stop
and exit-flag store, preserving captured values throughout the loop. The IR
proof extends its environment with a Boolean argument satisfying the same
structural property as the compiled closure input.

Eight native programs pass 192 comparisons. They cover bounds, initialization,
post-loop calls, captured words and flags, nested helper declarations, shadowing,
unused helpers, scalar-helper captures, Id result annotations, monadic bindings
and non-unit strides. Exact-syntax tests pass 3,456 comparisons and 2,304
invalid-input checks across binder kinds, result annotation depth, negation,
dependency flags and Boolean literals. The first focused runs passed without
source or proof corrections.

The general source-to-WASM theorem and all eighteen axiom audits pass. Native Lean/V8 agree on 1,441 inputs across 76 declarations, including 39 ranges. All 68 prior modules retain identical bytes. The full native corpus contains 794 declarations. Prior step and outer word-predicate tests pass 5,520 comparisons and 3,168 invalid-input checks.
