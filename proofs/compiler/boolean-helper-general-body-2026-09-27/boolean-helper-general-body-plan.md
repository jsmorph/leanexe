# General Boolean bodies in converted predicate helpers

The fixed probes reject nested helper bodies, wrapped nested bodies, an unused
nested helper, a nested body inside a proposition let, and Id input domains.
The first three share the same restriction: BooleanHelper.body is BooleanLocal,
although the compiler and source evaluation already recursively check its
Bool.toUInt64 conversion. Retain its exact raw Lean.Expr instead, preserving the
existing BooleanLocal exclusion and all helper type/domain checks. Let the
recursive compiler validate the body and continuation, including an unused body.

The source scopedPredicate/scopedBooleanPredicate rules, source totality,
acceptance, correctness and IR invariants already use recursive body proofs.
Keep those arguments and update only the raw-body projection where possible.
The parser's acceptance and soundness proofs must show exact source syntax,
without substituting, normalizing, or erasing helper syntax. Both recursive size
bounds should remain direct subexpression inequalities.

Do not change ordinary word-continuation predicate lets or Id input parsing in
this capability. The original proposition-let and identity-input probes record
those separate gaps. Check the native fixture, malformed body/domain/result
syntax, closures capturing outer words/flags/functions, repeated calls, nested
helpers with both argument kinds, wrapper layers and loop guards. Unsupported
unused bodies must remain rejected. Preserve the 44 shared WASM modules and
measure any byte changes rather than assuming equality.
