# Boolean-result helpers before Boolean loops

Boolean-result loops now admit captured UInt64-to-Bool and Bool-to-Bool helpers.
Each helper result is compiled through Bool.toUInt64. The source proof recovers
the corresponding native Bool, and the closure matching proof preserves that
zero/one encoding for every loop state. The return annotation may contain
standard Id layers. Unused helpers and both branches of their bodies are checked.

The source constructors and totality arguments reuse the established word-loop
predicate semantics. Existing Boolean-loop helper acceptance, source/IR matching
and structural invariants supply the proof structure. The first equation proof
failed because an outer match had not reduced before the validation-result case
split. An explicit reduction fixes both equations. The next focused build passes
source totality, extraction acceptance/soundness, correctness and invariants.
Public extraction and WASM admission then pass without changing the public
theorem or lowering.

Ten native declarations pass 240 comparisons, covering repeated calls, bounds,
nested closures, break/continue, captured public flags, strided ranges and Id
results. Raw syntax tests pass 64,512 comparisons, 55,296 invalid-input checks and
4,608 unused-helper controls. They vary both helper input kinds, public parameter
order, nested helper depth, return annotation depth, binder information, loops
and Boolean tails. Invalid input/result domains, wrong variable kinds, malformed
bodies including unused or unselected computations, and nonstandard Id heads or
universes are rejected.

Selected preceding word-helper, Boolean-input word-helper and let-annotation
tests are rerun. Complete compiler proof and bounded native Lean/V8 execution
checks follow this candidate. Other helper shapes, retained input annotations,
loop-containing continuations, broader helper/proposition bodies and full-dialect
compiler correctness remain open.

The complete compiler proof and nineteen axiom audits pass. Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1186 declarations.
