# General local helpers inside Boolean operands

After the current let-relation milestone is archived, run
boolean-inner-helper-probe.lean unchanged. Public Boolean program bodies gained
helper composition through the range/scalar dispatcher, but a Boolean operand
passed through Bool.toUInt64 still requires booleanLocalOperands? to recognize
its full expression. That parser only admits a named helper followed by an
immediate (possibly wrapped) call. Repeated calls in an inner let, Boolean saved
values, conditions, and Id.run results are likely gaps; measure first.

Avoid changing the existing named-call path or its emitted IR. Extend the `none`
branch of booleanLocalOperands? in extractScalarExprWith's conversion case to
recognize local function declarations and recursively compile their converted
Boolean continuation. Both recursive calls decrease: the helper body and the
continuation are children of the original inner let under scalarExtractionSize.
Validate the helper even when unused, retain exact function/lambda/result
annotations, and construct the existing typed ScalarBinding closure.

An independent source rule can describe this fallback without a parser premise:
record `beyond : ∀ expression : BooleanLocal, originalLet ≠ expression.expr`,
following SavedBooleanGuard.extended's established pattern. For source acceptance,
booleanLocalOperands_sound proves its parser result is none; for extraction
soundness, a none result and booleanLocalOperands_accepts produce this purely
syntactic exclusion. Old immediate-call syntax remains covered by BooleanLocal;
new helper declarations use the complementary source rule. Thus the union covers
all supported continuations without changing old parser priority or requiring
per-program semantic certificates. Do not add booleanLocalOperands? = none as a
source-semantic premise.

Start with UInt64-to-Bool and Bool-to-Bool local functions, potentially sharing a
source helper shape/type. Their function bodies use existing BooleanLocal and
EvalWith conversion meaning; the enclosing continuation may recursively contain
new helper declarations. Add converted-let EvalWith and SupportedWith constructors,
source totality, Boolean result encoding, accepts/correct/invariant/supported
proofs, then public/native/raw/V8 fixtures. Extend wrappers and general Boolean
composition only as separately confirmed gaps if their existing parser cannot
reach the new helper path. General word-result helpers inside Boolean operands
may need a subsequent constructor family. Retained Id input types should reuse
existing independent input shape/annotation proofs where possible.

The current production/test candidate is frozen until its evidence archive is
written and committed. Investigation files are scratch only.
