# Id annotations on Bool-input helpers

A new source annotation rule preserves matching arrow/lambda input types while
removing one exact Id layer for recursive checking. The inner source derivation
still validates the helper result, complete body and uses. This allows the
existing Boolean, word and step helper semantics to apply without adding a new
binding kind or changing lexical scope. The Boolean input parser has proved
acceptance and source reconstruction, and rejects mismatched domains or a
non-Boolean base type.

Source evaluation, support and totality pass for scalar, step and outer-loop
contexts. Head/literal/count exclusions include the new source form. The scalar
extractor removes one matched layer and checks the resulting declaration. Its
termination proof and wrapper equation pass. Scalar extraction soundness and
remaining step/outer-loop integration are in progress.

Scalar, loop-step and outer-loop acceptance, soundness, correctness and invariant
proofs now pass. The step wrapper equation required splitting the dependent
parser matches explicitly; direct simplification did not eliminate them. The
failed attempts are preserved with the successful focused build.

The native examples initially needed explicit Id.run at condition/arithmetic
uses and an explicit Bool decision at a helper argument. An additional retained
Id result annotation propagated into an HAdd output; an explicit UInt64 result
keeps that example within the current arithmetic grammar. Native testing also
found a separate existing gap: a Bool-returning helper call passed directly to
a word-returning Bool helper is not yet admitted. The nested fixture now tests
capturing that helper and calling it in the word helper body; the direct argument
case is preserved in the failed log and is the next capability.

The new native fixtures pass 180 comparisons. The raw syntax matrix passes
18,944 comparisons and 10,752 rejection checks across scalar, loop-step and
outer-loop scopes, all binder infos, one/three input Id layers, zero/two result
layers, both Boolean arguments, and used/unused helpers. Step results are checked
inside loop callbacks. Invalid checks cover mismatched domains, type confusion,
unsupported inputs/results, malformed Id heads/universes, bad arguments, missing
captures and unsupported bodies including unused helpers. The first matrix run
needed explicit Nat annotations for diagnostic interpolations; the corrected
matrix passes without compiler changes.

The focused prior suite passes 82,258 native/IR comparisons, 48,911 rejection
checks and 2,160 admission controls across fourteen files. One older Boolean
function test still expected a direct Bool helper condition to be unsupported,
although that capability was already proved. It now checks the native/IR result;
the three invalid declarations and twelve raw type checks remain. Its comparison
counter is checked explicitly. The failed old expectation is preserved.

The general compiler theorem and eighteen audits pass. Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1046 declarations.
