# Complete Boolean step-result bindings

Preserve the retained/show function probe and new direct, monadic, ignored-done
and conditional-binding probes before editing. Add a distinct result binding
kind to BooleanStep source and compiled contexts. Its semantics retain both
value and exit status; scalar projection is Unit, preventing accidental use as
a word or Boolean. Prove lookup, matching, totality and invariants for the new
kind without changing existing function bindings.

Add exact Boolean step-result annotation parsing for ordinary lets and standard
Id binds. Preserve arbitrary Id layers and check input/continuation domains,
output annotations and complete instance syntax. Bound computations are checked
even when unused. A done value exits only if returned by the callback; merely
binding or ignoring it must not exit. Preserve captures through nested bindings
and function scopes. Establish source totality, extraction correctness,
acceptance/support, invariants, public source-to-WASM correctness and V8
comparisons before adding functions taking complete step results.
