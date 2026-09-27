# Scalar bindings around Boolean helper scopes

Candidate `8039eaa1aec97197eeba797ffd7eeda3fd9059b4` admits ordinary UInt64 and Bool let bindings around
general Boolean helper scopes, including nested captures, unused values and
standard Id annotations. Both the bound value and continuation are checked.
The original binder positions, annotation, name and nondep flag are retained.

- Source, extraction and source-to-WASM correctness are proved; all 29 audits pass.
- Native Lean/V8 agree on 1,389 inputs across 73 declarations, including 38 ranges.
- 63 prior modules retain identical bytes; 0 changed.
- New tests pass 16,308 native/IR comparisons, 17,280 invalid-input checks and 384 admission controls.
- Prior tests pass 105,228 comparisons, 123,984 invalid-input checks and 1,344 admission controls.
- All six fixed scope-binding probes and ten Id-input probes compile.
- The native corpus contains 1,652 declarations.

[verification.json](verification.json) records commands and source/module hashes.
The [journal](journal.md) preserves failed proof attempts and corrections.
Monadic binding forms in these scopes and full-dialect correctness remain open.
