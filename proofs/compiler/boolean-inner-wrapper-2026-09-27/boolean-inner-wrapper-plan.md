# General Boolean wrappers around helper scopes

After the inner-helper proof and V8 archive is committed, rerun the unchanged
boolean-inner-helper-probe.lean. Direct conditions should now pass; the Id.run
example should still fail. Add native probes for pure, nested Id.run/pure,
metadata and conditions/loop exits around repeated helper-call scopes.

BooleanWrapper already independently describes exact Id.run, canonical Pure.pure
and metadata expressions, with native identity semantics and a structural body
size lemma. Extend the scalar Boolean conversion's fallback after both helper
parsers to a wrapper parser which checks the wrapper annotations, preserves the
body, and requires the syntactic complement of BooleanLocal. Avoid changing the
old BooleanLocal path and avoid parser premises in source semantics.

Prove wrapper acceptance/soundness and non-overlap with helper scopes. Recursively
compile Bool.toUInt64 applied to the body under the same bindings. Source
EvalWith/SupportedWith constructors, totality and Boolean result encoding can
reuse BooleanWrapper.denote_eq. The general BooleanScopeGuard added for direct
helpers should automatically carry this through scalar and step conditions.
Validate malformed result annotations and Pure instances, and unsupported bodies
under every wrapper. A discarded helper body must still be rejected. Preserve
old wrapper/immediate-call bytes and prove the compiler theorem before moving on.

If the wrapper parser would need to widen the existing helper body grammar,
keep that as a separate measured gap. The current helper scope admits a
BooleanLocal body and a recursively checked Boolean continuation.
