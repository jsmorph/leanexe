# Predicate helpers declared around loops

The outer-loop source grammar now admits reusable UInt64-to-Bool closures. Its
source evaluation is independent of compilation and retains captured words,
flags and functions. The range correctness proof matches each closure at every
accumulator/index/stop/exit state, so calls before, inside and after the loop
observe the same captured source values. The pure-scalar exclusion theorem
continues to separate a range-containing body from scalar-only extraction.

Source totality, extraction equations, acceptance, soundness, range evaluation
correctness and IR invariants pass. A source constructor initially used a result
name already bound by a function in this namespace; the result binder was renamed.
The invariant proof needed an explicit definitional change to restore Option.bind
after the outer extractor simplification. Neither fix changed the propositions.
The first Id-annotated fixture needed an explicit Bool expectation for Lean's
conditional elaborator. All three diagnostic logs are retained.

Eight concrete loops pass 192 native/IR comparisons. Systematic exact source
syntax adds 1,728 comparisons and 864 invalid-input tests. Cases cover repeated
calls in bounds, initial values, loop exits and final results, captured flags and
scalar functions, nested predicates, shadowing, unused helpers, Id annotations
and nonunit strides. Unsupported unused bodies and function/value type confusion
are rejected. The selected WASM suite has 41 declarations, extending the previous
33 with these eight loops. The general compiler theorem and engine checks follow
this candidate.

The general theorem and all sixteen axiom audits pass. Native Lean/V8 agree on
771 inputs across 41 declarations, including 21 ranges. All 33 previous modules
retain identical bytes. Prior loop-step tests pass 1,872 comparisons and 864
invalid-input checks. The full native fixture contains 759 declarations.
