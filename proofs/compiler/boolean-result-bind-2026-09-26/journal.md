# Id binds inside converted Boolean results

Boolean binding syntax now retains the standard Id Bind expression, its input
annotation, Boolean result annotation and continuation binder. The parser checks
that the input and continuation domain match. Bool inputs reuse Boolean binding
rules; UInt64 inputs reuse word binding rules. Both recursively check the converted
Boolean body, including calls to captured Boolean-input helpers. No new source
evaluation rule or runtime operation is needed.

The parser equation proof initially repeated a type-parser rewrite after simp
had already reduced it; removing that redundant rewrite completes the proof.
The parser round-trip proof adds both accepted input paths and rejects mismatched
domains. Source size bounds, scalar extraction, loop proofs and both invariant
modules pass. The first failed parser build is preserved with the successful runs.

New tests pass 3,764 native/IR comparisons, 3,072 invalid-input checks and 256
controls. They cover Boolean/word inputs, nested binds, captures, unused values,
negation, retained Id annotations, loop conditions and early exits. Rejections
cover wrong input/result types, mismatched domains, wrong universes, custom or
variable Bind instances and unsupported actions, including unused actions.
Prior binding and helper-result tests pass 42,768 comparisons, 28,032 invalid-input
checks and 2,368 controls. All test runs pass on their first invocation.

The general compiler theorem and eighteen audits pass. Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges. Eighteen shared modules retain identical bytes. The full native corpus has 976 declarations.
