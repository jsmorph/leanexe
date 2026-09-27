# Binary Boolean helpers around Boolean-result loops

Preserve the six fixed probes, including the Boolean-accumulator loop with a word
tail that may already compile through WordRange. Measure all six before edits.
Reuse the scalar binary predicate kind and helper recognizer in BooleanRange.
Source evaluation, support and totality follow the already proved WordRange rule.

Extend the existing two-word function declaration path only after word-result and
many-word recognition reject. Check the unused helper body, then compile the
Boolean continuation with the captured binary predicate closure. Keep the existing
scalar-conversion path first. Prove termination, the exact equation under scalar
rejection, complete acceptance, reconstruction, correctness at every loop state
and IR invariants. Current functional-induction cases start with scalar, word/flag
bindings, Id lets and helper declarations; inserting the new accepted branch
shifts old case 7 and above by one in all three proof files.

Complete native and syntax tests for bounds, initial flags, steps, early exits,
retained Id annotations, captures, nested helpers, unused bodies and empty ranges.
Keep any already admitted fixed probe labeled accurately. Register V8 fixtures,
run the complete proof and 45 axiom audits, compare prior module bytes, archive
measured counts and hashes, update task.md, commit and push before advancing.
Larger and mixed binary predicate signatures, multiple loops and the remaining
LeanExe dialect remain separate proof work.
