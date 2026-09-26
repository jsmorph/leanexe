# Saved decision proof journal

Saved `decide` values and ordinary or dependent Boolean-result proposition choices
share `PropositionGuard`. Replacing its canonical guard with `DecidedGuard` keeps
the original decision expression and its independent `GuardDecision` proof.
The non-Boolean condition check still separates this parser from the direct
Boolean condition parser. Exact proof-lambda domains remain required.

The existing scalar and loop-step lowering continues to use the retained guard
tree. Targeted parser, Boolean syntax, scalar correctness, step correctness and
source reannotation evaluation checks passed before the general compiler gate.
No new source rule assumes compilation succeeded.

Native examples exercise saved decisions, nested choices, captured flags,
helper bodies, Id actions, unused values and range break/continue. Constructed
syntax checks test preserved outer-variable indices, standard evidence and
both dependent proof-lambda domains. The previous decide and proposition-choice
fixtures also pass.

The general source-to-WASM theorem and all fourteen axiom audits pass. V8 agrees
with native Lean on 1,219 inputs across 73 declarations. All 62 preceding modules
retain identical bytes. The new focused tests pass 1,192 comparisons and 552
invalid-input checks. Full dialect correctness remains unfinished; Boolean-returning
local helpers need a source and compiler representation for their result type.
