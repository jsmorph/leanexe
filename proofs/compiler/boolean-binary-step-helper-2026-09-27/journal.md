# Binary Boolean helper declarations in word-accumulator loop steps

Five of six fixed native probes already compile after the scalar binary helper
increment. The early-exit probe rejects. Preserve all six unchanged. The new rule
handles a binary predicate declaration around a complete UInt64 ForInStep body,
using the existing scalar binary predicate value and compiled-binding kinds.

Source evaluation and totality pass 67 targets. The extractor tries the exact
binary-helper recognizer after the existing word and step function paths reject.
It validates the unused body with two placeholder arguments and captures the
current projected scalar environment. The continuation size bound proves
termination. Extraction passes 154 targets; the equation proof passes 155.

The generated induction theorem adds case 18 for the admitted declaration and
an extra rejection premise to case 17. Reconstruction normalizes locals.attach
with List.attach_map_val before using the continuation induction hypothesis.
Evaluation correctness, complete admission, source reconstruction and both IR
projection invariants pass 159 targets on the first combined attempt.
Function/range integration, focused tests, complete WASM proofs and V8 checks
remain. Boolean-accumulator loops and declarations outside loops remain separate.

Range/function integration passes 210 targets. The six unchanged probes now all
compile; five already compiled before this extension. Eight native loop examples
pass 192 comparisons. The syntax matrix passes 9,216 comparisons, 17,664 rejection
tests and 384 admission controls on its first Lean run. It varies result Id depth,
binder annotations, nondependency flags, wrappers, both junctions and four step
continuations. Asymmetric arguments and captured accumulators test ordering.
Every invalid case is checked with both a variable bound and an empty range.
The 82-declaration engine group retains all 74 prior binary-helper declarations
and adds the eight word-step fixtures. Complete WASM and V8 gates are next.

The complete source-to-WASM gate passes 3396 targets and all 38 audits. Passed 1595 native Lean / independent Wasm engine comparisons across 82 declarations.
74 prior modules retain identical bytes; 0 changed. All six fixed probes compile; five already compiled before this extension. Prior tests pass 20042 comparisons, 29524 invalid-input checks and 288 admission controls. Boolean-accumulator probes report 0 accepted and 6 rejected before the next increment.

The prior-test count parser initially omitted four rejection tests whose summary
spells out the number. The manifest and task count include those four checks.
