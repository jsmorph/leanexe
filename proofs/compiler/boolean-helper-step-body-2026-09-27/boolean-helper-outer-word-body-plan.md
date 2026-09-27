# General predicate bodies before word-result loops — subsequent capability

The fixed outerWord/outerBoolean probes declare a nested-body predicate before
a UInt64-result loop. Both remain rejected after the scalar body change. The
outer prefix in extractScalarRangeExitWith still parses BooleanLocal before
using the scalar Boolean conversion. Its Source.RangeExit binding rules already
require that scalar conversion for evaluation and support.

A bounded next step is to generalize only the RangeExit letPredicateFn and
letBooleanPredicateFn bodies to raw Lean.Expr, remove their redundant body parse,
and adjust equation/acceptance/support/correctness/invariant proofs. Preserve
NotScalar conditions, helper captures before the loop, unused-body validation,
Id annotation normalization and loop exit semantics. Native tests should include
helpers supplying bounds, initial values, loop bodies and tails; repeated calls,
shadowing, zero iterations, break/continue and native capture behavior.

Do not generalize every outer parser at once. ScalarBooleanRange uses the more
complex scalarBooleanRangeCompleteContinuation dispatcher, which also handles
loop-valued helpers and conditional continuations. ScalarBooleanWordRange and
ScalarWordRange have additional prefix grammars. Keep their raw-body gaps as
measured subsequent capabilities. First prove the word-result RangeExit prefix
and its independent WASM execution checks, then use fixed probes to pick the next
unsupported public form.
