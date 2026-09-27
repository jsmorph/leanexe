# Wrappers around conditional local loop calls

BooleanFunctionChoice now retains the conditional plus any finite nesting of
standard Id.run/pure/metadata wrappers and saved-result lets. Its condition,
evidence and branch getters preserve the underlying choice. Saved values do not
see their own binder, so captured helper references require no shifting.

The parser recursively checks each wrapper or saved-result let and still removes
the helper binder only from the core condition/evidence. Source syntax, exact
parser soundness/acceptance and arm-size proofs pass on their first build. Existing
complete-continuation extraction uses the same view getters, callbacks and loop
plan choice; no WASM lowering change is needed.

Native tests add Id.run, pure and show around conditional local calls, with both
input kinds, captures, nested local functions, break/continue, stride and Id
annotations. Raw tests combine these enclosing forms with nested choices and
forwarding, and reject invalid saved variables, types, wrapper heads and universes.
The equivalent-binding controls evaluate the same conditions and arguments
without a local helper declaration.

Source, extraction, correctness, invariant, public compiler and WASM admission
proofs pass on the first build. All ten native fixtures pass 240 comparisons.
Raw tests pass 96,768 native/IR comparisons, 59,904 invalid-input checks and 2,304
equivalent-binding controls. The parser/view extension required no changes to
the complete-continuation extractor or its loop-plan proofs. Existing conditional
fixtures now name the base syntax constructor explicitly after the view became
an inductive syntax. No proof or test failure occurred in this increment.

The complete compiler proof and nineteen axiom audits pass. Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1296 declarations.
