# Direct Boolean results in scalar helper declarations

Scalar UInt64-to-Bool and Bool-to-Bool helper declarations now compile the
complete Boolean body by recursively extracting Bool.toUInt64 expression.expr.
The exact Boolean result type and BooleanLocal parser remain required. The
source semantics use the same converted body and preserve its native Boolean
function result. Totality obtains that result through booleanConversion_result.

Correctness, acceptance and invariants reuse scalar closure proofs. The existing
scalarExtractionSize measure supports converted helper bodies; parser soundness
connects the parsed expression with the original lambda body for termination.
Soundness derives supported bodies directly from successful scalar extraction.
All focused proof modules pass on the first aggregate build.

Native and syntax tests pass 7,348 native/IR comparisons, 5,120 invalid-input
checks and 512 admission controls. They exercise both parameter kinds, chained
helpers, captures, used and unused bodies, negation, standard Id result wrappers,
metadata and malformed types or binding kinds. An explicit UInt64 annotation in
the native retained-Id example selects the intended equality instance.

This increment covers helper declarations in scalar bodies. Declarations whose
continuation directly produces a loop step or contains a loop remain separate
work. Boolean let/bind expressions within converted helper results also retain
separate parser and lowering limitations.

Prior helper, retained-input, bind and wrapper fixtures pass 13,924 native/IR
comparisons, 14,748 invalid-input checks and 852 admission controls. The first
prior fixture was mistakenly invoked with --run despite using #eval; its checks
passed before Lean reported a missing main declaration. The invocation was
corrected and all prior fixtures passed; both logs are retained.

The general compiler theorem and eighteen audits pass. Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges. Eighteen shared modules retain identical bytes. The full native corpus has 928 declarations.
