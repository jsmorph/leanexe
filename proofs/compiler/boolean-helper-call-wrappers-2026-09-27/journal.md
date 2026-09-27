# Wrapped named Boolean calls

The Boolean composition evidence is pushed as 9841bd80. The saved loop-bind
capture fixture still fails: return inserts standard pure around the call.

The source now represents the call tail separately, preserving any sequence of
standard Id run/pure and metadata wrappers. The Boolean lexical binding form
retains that tail, and its semantics remains the helper body's result. The parser
proves exact reconstruction, including domains, result types and wrapper syntax;
argument dropping still excludes references to the introduced helper.

The initial source size proof used field notation unavailable for this Nat
inequality. Replacing it with Nat.le_trans fixed the proof. Parser acceptance,
soundness and local syntax proofs then passed unchanged apart from carrying the
new tail field. The parser's decreasing-size proof implicitly used its equation
binder; naming it _parsed removes the unused-variable warning.

The full public compiler dependency build passes. A nested-Id native fixture
initially removed only one of two Id layers before a comparison, and Lean could
not synthesize BEq (Id UInt64). Explicitly running both layers fixed the native
fixture without changing compiler code. All 180 new native comparisons and
14,112 raw syntax comparisons pass, with 10,080 invalid-input checks and 2,016
parser/source and unchanged-IR controls. The unchanged saved loop-bind fixture
now passes all 240 native/IR comparisons.

The complete compiler proof and nineteen axiom audits pass. Native Lean/V8 agree on 549 inputs across 28 declarations, including seventeen ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1387 declarations.
