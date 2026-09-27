# Local functions returning Boolean loop steps

Two fixed conditional-action probes produce local continuation declarations
returning ForInStep Bool. Add unary word and Boolean step-returning functions,
including their lexical captures, repeated/nested calls and checked Id input
and output annotations. Keep ordinary scalar values/helpers separate from step
closures, so an invalid scalar call cannot reuse a step closure by accident.

Use a small BooleanStep binding/value layer with scalar, word-function and
Boolean-function alternatives. Project non-scalar values to Unit for scalar
subexpressions, preserving de Bruijn positions. Add typed lookup and source
projection lemmas; matching compiled closures quantify over admitted argument
expressions and preserve both value and done projections. Totality and invariant
relations should follow the existing word step bindings but remain specific to
Boolean step results. Do not refactor the existing word compiler.

Migrate the small Boolean step relation/extractor and their range entry points
to the new layer, wrapping existing scalar bindings. Prove direct cases again
through shared projection lemmas. Add source function/application rules, exact
input/output syntax parsers, acceptance/support, correctness and invariants.
Restore the fixed conditional-action probes unchanged. Check unused function
bodies, captures, wrong-domain calls and invalid instances, then complete the
source-to-WASM and V8 gates before adding step-result bindings.
