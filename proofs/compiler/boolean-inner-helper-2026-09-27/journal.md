# Inner Boolean helper scopes

The initial probe separated accepted saved Boolean values from rejected direct
conditions and general Id.run wrappers. The public range dispatcher already
handled saved values. The scalar conversion parser only recognized the exact
named-helper/immediate-call grammar, so repeated calls in an inner scope could
not reach its closure compiler.

The new BooleanHelper source shape preserves exact helper annotations and a
syntactic exclusion from BooleanLocal. Source semantics do not refer to a parser
or to compilation success. Parser soundness/acceptance establish the complement
of the existing grammar. The scalar converter checks even unused helper bodies,
builds the existing typed closure, and recursively checks the continuation.
The old BooleanLocal path retains priority and its previous lowering.

Direct conditions needed an additional BooleanScopeGuard path after the closed
comparison, compound guard and BooleanLocal paths. Its independent syntax checks
the original Boolean truth proposition and standard decision; dependent choices
also require the exact proof domains. Source totality uses the proved zero/one
Boolean conversion result. Correctness and IR invariants use the existing word
comparison with one. The first scalar-equation attempt used simp under dependent
matches; explicit rewriting reduced these matches. Adding source constructors
also required extending the impossible-form cases in literal/range-count proofs.

Focused scalar syntax tests passed 1,344 native/IR comparisons, 1,248 invalid-input
checks and 32 controls. Scalar proofs and these tests were committed and pushed
as 63c4f656 before extending loop steps. Tests preserve exact input/result types,
captures, nondependent flags, binder metadata, nested Id result types, unused
bodies, decision evidence and proof domains.

The first public native test retained a failure at rangeInnerHelperExit: step
conditions still used only the prior guard grammar. The step converter now
reuses BooleanScopeGuard and the scalar conversion, with independent source
rules and proofs for both emitted projections. This is needed to preserve the
accumulator and break/continue decision together. A correctness-proof binder
order mismatch was diagnosed by printing the source constructor signature and
fixed without changing the semantics or fixture.

General Id.run-wrapped helper scopes remain a separate confirmed gap. They are
not claimed by this increment. All diagnostic logs and failed attempts are kept
with the eventual compiler and V8 evidence.

The existing helper-composition syntax test assumed that public compilation and
the explicit Boolean range dispatcher produced identical Func structures. The
new scalar converter admits some of those bodies directly, so public compilation
uses the existing scalar fast path instead of a zero-iteration range plan. The
original test and failure are retained. The test now compares the native value,
public result and explicit range result, and also evaluates unused-helper controls
instead of requiring identical plans. This adds 8,960 value comparisons. Byte
comparisons will record any affected prior modules rather than require unchanged
bytes for a deliberately expanded scalar path.

The scalar and step native tests pass 180 comparisons; raw tests pass 3,136
value/exit comparisons, 2,176 invalid-input checks and 64 admission controls.
Four adjacent tests pass 123,360 comparisons, 78,424 invalid-input checks and
4,448 controls. The production candidate 4bc6fa2a passes the source-to-WASM
proof and all nineteen axiom audits (3,363 build targets). A test-only follow-up
adds six prior public helper declarations to the independent V8 group; production
and theorem source files are unchanged from the proved candidate.

The general compiler proof and nineteen axiom audits pass. Passed 993 native Lean / independent Wasm engine comparisons across 54 declarations.
40 prior modules retain identical bytes; 4 changed. The full native corpus contains 1417 declarations.

The changed prior modules are publicBoolHelpersWrapped (1242 to 1184 bytes),
publicBoolHelpersRepeated (1295 to 1237), publicBoolHelpersNested (1182 to 1123),
and booleanPropRelationHelpers (1324 to 1266). All four pass native/V8 execution.
The group includes 25 range declarations and 600 range input comparisons.
