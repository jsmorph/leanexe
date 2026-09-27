# Boolean setup before Boolean loop results

The preceding word-setup capability passed the complete compiler proof, nineteen
axiom audits and 599 native/V8 comparisons. This increment adds exact Bool let
bindings and standard Boolean-to-Boolean Id binds before Boolean loop bodies.
Bind input/output annotations may retain Id layers and the continuation domain
must match the input. Scalar conversion checks the flag action and recovers its
native Boolean value before extending the loop's captured bindings.

The source evaluation/support rules are independent of IR. The extractor compiles
the Boolean conversion, then recursively handles the loop body with a typed flag
binding. Existing word setup, loop-result binding and WASM theorem statements
are retained. Id-annotated let domains and outer helpers are subsequent work.

Source totality, exact annotation parsing, acceptance, evaluation and invariant
proofs pass on the first build, followed by public application/admission. The
syntax matrix passes 24,192 native/IR comparisons, 13,824 invalid-input checks and
1,728 lexical setup controls. The first native conditional-bind fixture failed.
Inspection of the elaborated source shows Lean generated a __do_jp local function
whose body contains the loop, and an outer conditional calls that continuation.
This requires loop-containing local function/continuation support, outside the
current scalar flag setup rule. The failed fixture and full elaborated term are
preserved. The conditional-value fixture uses pure (if ... then ... else ...),
which keeps the loop outside the scalar conditional. General conditional-action
continuations remain recorded as subsequent compiler coverage.

The adjusted ten native declarations pass 240 comparisons. Expanded annotation
checks bring the raw syntax matrix to 24,192 comparisons, 24,192 invalid-input
tests and 3,456 lexical/unused setup controls. Wrong bind domains, output kinds,
universes, instances and heads are rejected even when the bound flag is unused.
The valid unused-binding control produces identical IR to the original loop.

The complete compiler proof and nineteen axiom audits pass. Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1146 declarations.
