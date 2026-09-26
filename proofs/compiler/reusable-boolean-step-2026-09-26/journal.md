# Reusable predicate helpers in loop-step bodies

The scalar predicate-function binding can be embedded directly in a step binding,
so the step environment preserves the same typed closure and captured scalar
values. New independent step evaluation/support rules describe the Boolean helper
and the continuation that uses it. The extractor distinguishes UInt64, Bool and
ForInStep result annotations and checks every helper body before compiling the
continuation.

Source totality, extraction equations, acceptance, soundness, evaluation
correctness and preservation of both IR step projections pass. An equation proof
initially left a source-pattern exclusion goal untouched; applying the existing
type-shape simplification to both goals solved it. The first soundness proof
needed the existing List.attach_map_val equality to remove bookkeeping from the
function-induction hypothesis. Both diagnostic logs are retained.

Six concrete loop fixtures pass 144 native/IR comparisons, covering break,
continue, captured values, nested predicates, step-valued helper captures and
unused helpers. The selected WASM group contains these new loops, the ten reusable
scalar helpers, and the 17 existing guard-core declarations. This keeps execution
checks focused while exercising earlier loop and guard forms.

Systematic exact-syntax tests add 1,728 native/IR comparisons and 864 invalid-input
checks across binder annotations, nested Id result annotations, negations and let
flags. The tests exercise both yielding and early exit through complete range
functions. The initial fixture used positional construction without the guard's
third field; record construction uses its defined truth-condition default.
The general theorem and selected engine checks follow this candidate.

The general theorem and all sixteen axiom audits pass. Lean/V8 agree on 579
inputs across 33 declarations, including 13 ranges. All eleven modules shared
with the preceding scalar-helper archive retain identical bytes. The scalar
helper tests still pass 1,148 comparisons and 864 invalid-input tests.
