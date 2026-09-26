# Comparison operand proof journal

The source relation is independent of extractor success. Standard arithmetic
heads carry a native UInt64 operation; related heads carry the same operation.
Numerals carry matching native numbers and independent standard-instance
witnesses. Exact subexpressions and corresponding metadata wrappers preserve
existing expression structure. Evaluation is proved in both directions against
the existing `EvalWith` relation.

Direct dependent elimination of arithmetic and numeral evaluations initially
failed on unequal expression names and unresolved type indices. Generalizing
the indexed expression before elimination supplied ordinary expression
equalities. Shared arithmetic-head and numeral inversion lemmas then reduced
the semantic proof to structural induction. The failed drafts and diagnostics
are retained as worked examples.

The recognizer has checked soundness and acceptance theorems. It recognizes
standard arithmetic heads, compares primitive identities, recursively checks
operands, and validates numeral types and instances. A small injectivity lemma
distinguishes all ten native binary operations. Comparison evidence uses
separately elaborated operands while retaining the original propositions in
negation evidence. Candidate operands are extracted from the expected decision
shape, then the entire evidence expression is checked exactly.

The new comparison form shares existing guard lowering. Original canonical
comparisons retain their path. Boolean-local guard exclusion now also proves
that the annotation fallback cannot recognize a Boolean-local condition.

The first complete proof run found a separate main integration issue: shared
scalar programs retained structured-control result types while the general
compiler translation omitted them. The translation and its binary witness now
retain i64/i32 result types. No instruction bytes or compiler semantics were
changed by that repair. The focused translation target passed before the
complete proof was rerun.

This increment covers ordinary scalar and loop-step comparison branches.
Compound guard evidence, dependent branch evidence and saved decisions with
differently annotated operands remain subsequent work. Full LeanExe dialect
compiler correctness is not established by these scalar proofs.
