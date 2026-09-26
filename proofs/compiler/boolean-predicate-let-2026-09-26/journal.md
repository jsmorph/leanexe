# Direct scalar Boolean lets

The propositional-choice increment is complete before this capability changes
production code. Direct Boolean lets can use the recursively checked zero/one
conversion and install its result as a Boolean binding. The source rule will
require an encoded Boolean evaluation of the bound expression and use that
native Boolean in the body. This permits reuse of the completed call, junction,
equality and choice proofs while retaining checks on unused bound expressions.

The ordinary expression size counts constant-name strings. A converted bound
value can therefore exceed a minimal let wrapper in that measure. A scratch
checks the exact sizes and a narrowly adjusted measure that ignores only the
outer Bool.toUInt64 wrapper. The measure is at most the original size, and the
existing parser lemmas already prove children smaller than the unwrapped Boolean
expression. The function's behavior does not depend on the chosen measure.

Kernel reduction gives 1176 for the minimal converted variable and 425 for the
minimal Boolean let, confirming that the original measure is unsuitable here.
The measure definition must be noncomputable because Lean.Expr's kernel size
instance has no compiled implementation. The scratch then passed. The first
termination integration used a simplifier without an optional-progress guard;
its no-progress diagnostics were fixed. A second pass needed simp_wf after
unfolding the measure so arithmetic sees constructor-size equations. All existing
recursive bounds then passed. The logs preserve these diagnostics.

The let source rule was replaced with recursive encoded-value evaluation and a
Boolean body binding. This removes duplicate argument/environment proof work;
totality obtains the flag from booleanConversion_result. Extraction compiles the
conversion and body directly. Correctness, acceptance, soundness and IR invariant
proofs passed on the first aggregate build. The prior lowering is preserved for
previously admitted Boolean values.

Native examples cover saved calls, shadowed flags, nested calls, Eq/Ne decisions,
Boolean and propositional choices, scalar helper captures, unused bindings,
retained Id annotations and scalar subexpressions inside loop bounds, steps and
results. Raw tests vary dependency flags and cover invalid used/unused values,
word/function/Boolean confusion and both plain and loop-nested scalar contexts.
The seven preceding scalar syntax fixtures moved valid unused bindings into
admission controls; those cases are no longer listed as invalid. Their input
coverage is retained. Focused tests pass 16,052 native/IR comparisons, 11,468
invalid-input checks and 280 controls. Direct step/outer Boolean bindings and
other Boolean contexts remain subsequent increments.

All selected prior tests pass: 33,330 native/IR comparisons and 27,913 invalid-input
checks. Predicate fixtures include 1,436 explicit controls; older Boolean-let
fixtures additionally check 32 valid bindings. An initial test command used the
singular filename scalar_boolean_local.lean; the existing plural filename was
then run successfully, along with the Boolean-let and annotation fixtures. The
command failure is retained. The full theorem, eighteen audits and focused
28-declaration engine group are next for this candidate.

Selected prior tests pass 33,330 comparisons and 27,913 invalid-input checks, with
1,468 admission controls. The general compiler theorem and all eighteen axiom
audits pass. Native Lean/V8 agree on 479 inputs across 28 selected declarations,
including ten ranges. All eighteen modules shared with the propositional-choice archive
retain identical bytes. The full native corpus contains 864 declarations.
