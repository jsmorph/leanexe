# Unit-prefixed helpers before Boolean loops

Helpers before Boolean-result loops now admit Unit/PUnit followed by a UInt64
parameter and a word result, including standard Id result annotations. The unit
binder remains present in the source semantics and in the captured environment;
it cannot be used as a word. The compiler checks the body before extracting the
continuation, even for unused helpers.

The existing UnitSyntax description supplies the two accepted spellings and
standard values. Source totality, extraction acceptance/soundness, source-to-IR
matching and structural invariants follow the established word-loop helper
proofs. The matching proof extends the environment with the unit value before
the word argument, preserving every outer capture across loop state changes.
The first focused proof build and the public/WASM-admission build pass.

Ten native declarations pass 240 comparisons for repeated calls, bounds,
initialization, nested helpers, captured public flags, break/continue, stride,
retained Id results and shadowing. Raw syntax tests pass 16,128 comparisons,
18,432 invalid-input checks and 1,152 unused-helper controls. They cover both
Unit spellings, binder forms, captured values, nested helpers, result annotations,
loop forms and Boolean tails. Invalid cases include unsupported bodies,
unit-as-word use, mismatched domains, nonstandard Unit names and invalid PUnit
universes. All new execution tests pass on the first attempt.

Selected preceding multiple-argument, input-annotation and predicate-helper tests
are rerun. The complete compiler proof and native Lean/V8 checks follow this
candidate. Loop-containing continuations, broader helper/proposition bodies,
more general loop compositions and full-dialect compiler correctness remain open.

The complete compiler proof and nineteen axiom audits pass. Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1216 declarations.
