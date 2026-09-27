# Retained Id inputs in converted Boolean helper scopes

Ten fixed examples reject before the implementation change. The first baseline
fixture supplied a proposition where a Bool was expected; adding explicit decide
made the fixture well typed. The corrected baseline rejects all ten examples.
The older identityInput probe remains unchanged.

BooleanHelper now retains the exact domain and an independent PublicArgument.Domain
certificate. The parser reuses the proved input recognizer, requires identical
arrow/lambda domains, and retains standard Boolean result checks. The helper's
value semantics still uses the base UInt64 or Bool, since standard Id is identity.
Arbitrary body/continuation syntax and lexical captures are unchanged.

The focused helper proof passes 67 targets first try. Three now-unused simp
arguments were removed before checking the full extractor. No extraction or
backend algorithm change is required beyond generalized helper recognition.

The full extractor build passes 205 targets first try. Eight of ten fixed probes
compile, and the raw syntax matrix passes 32256 comparisons, 48384 invalid-input
checks and 768 admission controls. The two failures identify different boundaries.
The capture example's word let around a general Boolean helper already rejects
with bare inputs; its original probe is preserved for the next capability. The
native corpus checks lexical capture with that word binding outside the Boolean
conversion. The proposition example works with bare inputs but its retained
proposition-let type parser rejects Id inputs. That parser now gets a separate,
independently typed predicateId case, preserving its bare input cases.

The proposition-let source extension checks immediately. Its acceptance proof
needed an explicit split of a proof-dependent match; simp alone did not rewrite
that match. With the split, both source and recognition pass 21 targets.

Rebuilding the full ScalarFunc dependency target after the proposition grammar
change reached the 180-second aggregate limit after target 195, without a proof
error. This rebuild invalidates the guard-dependent source tree. Verification is
split at the remaining BooleanWordRange and WordRange module boundaries before
checking the final function module; unchanged completed dependencies stay cached.

The remaining module builds pass at the smaller boundaries. Nine of ten fixed
probes now compile, including the proposition case. Ten native fixtures pass
180 comparisons; the Id predicate-let syntax matrix passes 72576 comparisons,
75600 invalid-input checks and 576 admission controls on its first attempt.

The archive's initial byte-equality assertion caught one changed prior module.
publicBoolHelpersInputId shrinks from 1277 to 1219 bytes. Its newly supported
converted helper inputs let extractScalarFunc choose direct scalar extraction,
where it previously used the Boolean range fallback with a zero-iteration loop.
The disassembly removes that loop and three unused locals; the result expression
is unchanged. The complete proof and V8 comparison pass for the new output.
Sixty prior modules are identical and this one is smaller. Both disassemblies
are archived; the archive records this reviewed change instead of requiring
byte identity for a program that now uses a more direct proved path.
