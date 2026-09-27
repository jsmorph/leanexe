# Standard wrappers around local Boolean loop calls

A source BooleanCall records a direct call or any finite sequence of standard
Boolean Id.run, pure and metadata wrappers. The local-function syntax preserves
that call shape, function annotations, argument binder and captured references.
The parser returns the shape and the original argument outside the function
binding. Its exact soundness and acceptance proofs use the existing wrapper
parser and the direct-call binder-removal proof.

The scalar helper path still runs first. The direct fallback now uses the wrapped
call parser; extraction's recursive body processing and WASM lowering are unchanged.
The source application constructors carry the independent call shape. Their
source totality, extraction acceptance/support, correctness and invariants pass,
as do public extraction and WASM admission.

The first wrapper equation proof required another split for the parser's dependent
match. The continuation success lemma needed an explicit BooleanCall existential
type, then the correctly separated existential binder syntax. The resulting
public proof build passes. No new axioms or admitted proofs are used.

Ten native tests restore the saved Id.run failure and add nested wrappers,
Boolean/word arguments, captured helpers, nested local functions, break/continue,
stride and repeated Id input/result annotations. Raw syntax tests combine wrapper
forms and depths, all binder forms, both public argument orders, scalar/mixed/loop
bodies and direct/public extraction. Invalid checks include self-reference under
wrappers, wrong result/input kinds, custom heads and instances, and bad universes.

All ten native cases pass 240 comparisons, including the restored saved Id.run
case. The raw fixture initially used the reserved word `universe` as an argument
name; renaming it to `level` fixes the fixture. The failure is retained. Raw tests
pass 96,768 native/IR comparisons, 55,296 invalid-input checks and 3,456 binding
controls. The preceding direct-call syntax tests pass unchanged.

The complete compiler proof and nineteen axiom audits pass. Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1256 declarations.
