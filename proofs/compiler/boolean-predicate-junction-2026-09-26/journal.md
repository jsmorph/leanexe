# Conjunction and disjunction of Boolean-input predicate calls

The new source rule checks both converted children independently and evaluates
the native Boolean conjunction/disjunction, followed by its Not wrappers. A typed
function witness distinguishes this extension from the existing word-input
predicate grammar. Source totality obtains encoded Boolean results from the
previously checked conversion-result lemma.

The extractor detects a referenced Boolean-input function before recursively
compiling each junction child. Expressions containing only existing word-input
predicates keep their old lowering. The new result uses the already proved
word-level Junction primitive followed by encoded negation. Separate lookup,
absence, child-size, execution and structural lemmas keep the extraction proof
small.

The initial size proof unfolded only its left goal; unfolding BooleanLocal.expr
in both goals resolved the failure. The first aggregate extraction check found
that the false dispatcher branch needed explicit if_neg reduction before
unpacking the compiled result. That local proof change passed the next build.
All diagnostics are retained. Correctness rejects the alternative lowering by
its typed predicate witness; it does not assume that the lexical matching
relation implies equal environment lengths.

Examples cover mixed word/Boolean predicates, captured flags, nested calls,
compound arguments, converted calls in helper bodies, Id computations, break,
continue, loop bounds and final values. Exact-syntax tests cover both junctions,
constant true/false branches, repeated negation and binder/result annotations.
Both operands are checked even if a junction's result is already determined.
Focused tests pass 16,052 native/IR comparisons and 11,520 invalid-input checks.
Prior nested-call tests pass 12,084 comparisons and 8,640 invalid-input checks.
The general compiler theorem, audits and independent engine gate are next.

The general compiler theorem and all eighteen axiom audits pass. Native Lean/V8
agree on 1,981 inputs across 106 declarations, including 51 ranges. All 96 prior
modules retain identical bytes. The full native corpus contains 824 declarations.
