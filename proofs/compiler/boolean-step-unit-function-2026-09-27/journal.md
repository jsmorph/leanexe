# Unit-prefixed Boolean step continuations

The unchanged generated Unit-to-Bool-to-Boolean-step continuation rejects through
both direct and environment extraction. Six additional native probes cover Unit,
PUnit, retained Id types, captures, nesting and unused functions. Their first run
has two unresolved PUnit universes; explicit PUnit.{1} annotations fix those
source errors. All six then reject before the extractor is extended.

A distinct unitBooleanFunction kind records UnitSyntax. Source/IR typed lookup
keeps Unit and PUnit separate; scalar projections retain binder positions without
exposing step-valued functions as scalar values. Matching, totality and invariant
projections pass 21 targets on the first build. The exact source helper shape
retains both type/value binders, Boolean input/output annotations, body and
continuation. Source evaluation supplies the flag at index zero and unit at index
one. Source totality passes 69 targets on the first build. Compiler recognition,
extraction and end-to-end proofs remain.

Recognition definitions move into ScalarBooleanStepSyntax so their proofs can be
checked separately from compiler induction. Both unit-domain and unit-value
soundness proofs need explicit unfolding before pattern splitting; direct
fun_cases did not reduce the hypothesis. Binary-helper rejection also requires
splitting its Boolean-local guard. Recognition passes on the second attempt.
The extractor's dependent recognizer matches do not reduce using simp alone;
explicit splitting proves both declaration equations. The isolated extractor,
termination and equations pass on the second attempt. Its generated induction
has 30 cases. General evaluation correctness, complete acceptance, source
reconstruction and IR invariants pass 154 targets on the first combined build.
Seven recognition/native-application axiom audits are added, bringing the gate
from 38 to 45. Integration and tests remain.

Function/environment integration passes 216 targets. The unchanged generated
continuation and all six fixed native probes compile. Eight native fixtures pass
192 comparisons. The syntax test first fails while formatting UnitSyntax in error
messages; using reprStr fixes that test-only issue. The matrix then passes 18,432
comparisons, 39,936 invalid-input checks and 768 recognition controls. It covers
both unit spellings, two input and three output annotation depths, independent
binder annotations, nondependency flags, wrappers, nested functions and saved
step results with changed done/yield behavior. Every invalid case is rejected in
both a variable range and an empty range. The 98-declaration V8 group retains all
90 prior declarations and adds eight fixtures. Complete WASM and V8 gates follow.

The complete source-to-WASM gate passes 3397 targets and all 45 audits. Passed 1979 native Lean / independent Wasm engine comparisons across 98 declarations.
90 prior modules retain identical bytes; 0 changed. The generated continuation and all six additional fixed probes compile; all rejected before this extension. Prior tests pass 30384 comparisons, 28896 invalid-input checks and 384 admission controls. Outer word-loop probes report 0 accepted and 6 rejected before the next increment.
