# Retained Id input annotations on helpers before Boolean loops

A source constructor preserves standard Id layers on a helper's declared input
and lambda input. Its premise is the corresponding helper with one layer removed.
The extractor requires those input domains to match, removes one standard Id
layer and recurses on a smaller expression. Existing helper checks establish the
base input/result types, body support and lexical captures. This covers every
number of layers without adding four copies of the helper proofs.

The first focused proof build exposed two proof-script issues: the equation had
already reduced reflexive equality to True, and functional induction had already
substituted equal domains. Reducing the remaining if and using the actual case
parameters resolves them. The next build passes source totality, extraction
acceptance/soundness, correctness and invariants. Public extraction and WASM
admission pass without changes to lowering.

Ten native declarations pass 240 comparisons. They cover all four combinations
of word/Boolean inputs and results, repeated Id layers, wrapped arguments and
results, loop bounds, break/continue, mixed helper captures and shadowing. Raw
syntax tests cover one and three retained input layers, with all four helper
kinds, nested helpers, public parameter order and multiple binder/result forms.
They pass 64,512 comparisons, 73,728 invalid-input checks and 4,608 unused-helper
controls. Invalid controls include mismatched input domains and depths,
nonstandard Id heads/universes, unsupported base types and invalid helper bodies.
All new execution tests pass on their first run.

Selected preceding predicate syntax, word-helper and Boolean-input word-helper
tests are rerun. The complete compiler proof and native Lean/V8 checks follow
this candidate. Helpers with multiple word arguments and Unit arguments,
loop-containing continuations, broader helper/proposition bodies and full-dialect
compiler correctness remain open.

The complete compiler proof and nineteen axiom audits pass. Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1196 declarations.
