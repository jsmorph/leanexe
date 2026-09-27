# Unary word helpers before Boolean loops

The preceding Id let-annotation capability passed the complete compiler proof,
nineteen audits and 609 native/V8 comparisons, and its evidence is committed.
This increment adds local UInt64-to-UInt64 helpers declared before Boolean loops.
Helper results may retain standard Id layers, and pure scalar bodies can capture
prior words, Boolean flags and word helpers. Calls may supply bounds, initial
values, loop steps and the final Boolean computation.

The independent source relation evaluates a native word function for every input,
then the Boolean loop body under its closure. Compilation validates the helper
body even when unused and compiles calls against the captured lexical bindings.
The evaluation proof preserves the closure for every loop store. Boolean helper
inputs/results, other arities and loop-containing continuations remain later work.

Source totality, acceptance, extraction correctness and invariants pass on the
first focused build (154 targets), followed by public application and admission.
Ten native declarations pass 240 comparisons. The raw syntax matrix passes
32,256 comparisons, 27,648 invalid-input checks and 2,304 unused helper controls.
It varies nesting, Id results, arrow/lambda binder info, captures and loop/tail
forms. Invalid unused bodies, wrong function domains/results, malformed Id heads,
wrong binding kinds and unsupported dead bodies are rejected. Valid unused helper
declarations produce identical IR. All first attempts for this increment pass.

The complete compiler proof and nineteen axiom audits pass. Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1166 declarations.
