# General predicate bodies before word continuations — subsequent capability

After converted helper bodies are admitted, the fixed proposition-let probe still
fails because its validation operand is an ordinary let ending in UInt64 zero.
The ordinary scalar letPredicateFn/letBooleanPredicateFn rules already recursively
check and evaluate Bool.toUInt64(body), but carry BooleanLocal instead of raw Expr.
The scalar parser repeats the same BooleanLocal restriction before recursion.

A bounded next step can generalize these two scalar rules to raw Lean.Expr and
remove the redundant BooleanLocal parse in the corresponding UInt64/Bool lambda
branches. Preserve BooleanType result parsing, exact input/lambda domains and
mandatory zero-input body validation. Update both equation lemmas and their
source acceptance/correctness/totality/invariant cases. The two removed parser
failure cases will change the functional induction case numbers; inspect the
new generated induction signature rather than guessing their complete mapping.

Keep the separate Step/Range source syntax and parsers on BooleanLocal initially.
Their existing scalar fallback proofs can apply the new scalar equations at
expression.expr; explicit constructor arguments may need that projection. Do
not broaden all loop helper declarations in the same step. Test scalar word
continuations and proposition lets, including those used as scalar operands in
loop guards/tails, so each newly claimed form is checked through WASM. Preserve
separate failing probes for loop-step and outer-loop helper declarations.

Termination remains structural under scalarExtractionSize_conversion. Source
Boolean conversion result and totality lemmas already supply zero/one outputs
for raw body recursion. No new source meaning or erased body check is needed.
