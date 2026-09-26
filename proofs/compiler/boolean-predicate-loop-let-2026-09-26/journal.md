# Direct Boolean lets in loop-step and outer-loop bodies

The checked scalar conversion now supplies bound values in step and outer-loop
Boolean lets. Source rules evaluate the encoded value, recover its native flag,
and extend the appropriate Boolean environment. Step values project to scalar
values for the bound computation. Outer-loop correctness preserves the captured
flag across all accumulator/index/stop/done stores. Both extractors call the
separately terminating scalar extractor, so their termination measures are
unchanged. The same changes simplify acceptance, soundness and source totality.

The first aggregate proof passed all components except an outer-loop invariant
branch: its local environment-extension helper was specialized to word bindings.
An explicit Boolean extension fixed that branch. The focused retry passed; all
diagnostics are retained. No axioms or admissions were introduced.

Native examples cover saved flags controlling break/continue, Boolean and
propositional choices, nested calls, captures, shadowing, unused bindings, Id
annotations, helper bodies, bounds/stride, initial state and final results. Two
Id-annotated flags initially appeared directly as if conditions, which Lean does
not coerce to Prop. Explicit Eq Bool conditions retain their intended syntax and
compile; the initial elaboration errors are preserved.

Eight prior step fixtures moved newly supported unused Boolean lets from invalid
lists into admission controls. The analogous outer fixtures bind a flag then use
its slot as a UInt64 accumulator; those inputs remain invalid. They were retained,
and new controls test correctly scoped used and unused outer bindings instead.
Raw tests check saved-flag indices separately from function and word indices,
with binder/dependency/negation and nested Id annotation variations.

Focused tests pass 3,264 native/IR comparisons and 1,672 invalid-input checks,
including eighty admission controls. The selected engine group contains 26
declarations, including seventeen ranges; eighteen modules are shared with the
scalar-let archive. The full theorem, audits and engine check are next.

All selected prior tests pass: 51,154 native/IR comparisons, 31,295 invalid-input
checks and 1,992 controls. Source files and test fixtures are ready for the full
compiler theorem and focused native Lean/V8 check.

The general compiler theorem and all eighteen axiom audits pass. Native Lean/V8
agree on 521 inputs across 26 selected declarations, including seventeen ranges.
All eighteen modules shared with the scalar-let archive retain identical bytes.
The full native corpus contains 872 declarations.
