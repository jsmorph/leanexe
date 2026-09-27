# General predicate bodies in the remaining word-result outer grammars

Four unchanged probes reject nested predicates around Boolean-derived word
results and word conditionals. Both predicate input kinds are represented.
ScalarBooleanWordRange and ScalarWordRange still parse a BooleanLocal body before
their scalar conversion checks. Generalize their source Eval/Supported rules,
parser, acceptance equations, support, correctness and invariants to raw bodies.
Keep exact types, initial unused-body validation and closure capture behavior.

The parser change removes an optional parse rather than an explicit match, so
functional induction should retain its case numbering. Verify the generated
cases in the focused proof build instead of assuming additional indices.
Run each outer extraction module separately to keep elaboration bounded.

Test both outer grammars with both input kinds, used and unused helpers,
conditional branches, wrappers, captures and final computations. Retain the four
initial probes unchanged. After native/IR syntax checks, register the declarations
and run the general source-to-WASM proof and independent WASM comparison gate.
Keep Boolean accumulators and multiple dynamic loops as separate open work.
