# Binary Boolean helpers around word-result loops

All six fixed probes reject before this increment. They cover helper use in loop
steps, bounds, initial accumulators, early exits and final results, plus an unused
helper. Preserve these probes unchanged. Add a WordRange source rule for the
existing BooleanBinaryHelper and scalar binary predicate kind. Evaluate both
arguments in source order and retain captured values across every loop state.
Prove source totality before extending extraction.

After the existing scalar, range-exit and Boolean-derived-word paths reject,
try the exact binary Boolean helper parser when the two-word helper has neither
a word result nor a many-word signature. Validate the unused body with two word
placeholders; compile the continuation under the captured closure. Reuse parser
acceptance, soundness and size bounds. Prove the extraction equation under the
three existing-path rejection premises; retain existing accepted paths.

Prove complete admission, source reconstruction, correctness at all loop stores
and IR invariants. Run the fixed probes and focused native/syntax tests covering
captures, bounds, initial values, tails, unused functions, early exits, malformed
annotations, argument order and empty ranges. Register native/V8 fixtures, run
the complete source-to-WASM gate and all 45 existing audits, compare prior modules,
archive evidence, update task.md, commit and push before the next capability.
Boolean-result outer loops and multiple loops remain separate increments.
