# Direct scalar applications around Boolean helper scopes

Candidate `dc88e38b8edee7b7ce72cd4b6d2e7604ad974a44` admits direct UInt64 and Bool lambda applications around
general Boolean helper scopes, including nested captures, unused arguments,
conditional arguments and standard Id annotations. The complete lambda syntax
and scalar domain are checked.

- Source, extraction and source-to-WASM correctness are proved; all 33 audits pass.
- The native beta-reduction equation has no axioms.
- Native Lean/V8 agree on 1,389 inputs across 73 declarations, including 38 ranges.
- 63 prior modules retain identical bytes; 0 changed.
- New tests pass 16,308 native/IR comparisons, 21,888 invalid-input checks and 384 admission controls.
- Prior tests pass 32,832 comparisons, 48,384 invalid-input checks and 768 admission controls.
- All six fixed application scope probes compile.
- The native corpus contains 1,672 declarations.

[verification.json](verification.json) records commands and source/module hashes.
The [journal](journal.md) preserves failed proof/test attempts and corrections.
Two-argument predicate helpers and full-dialect correctness remain open.
