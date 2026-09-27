# Retained Id inputs in Boolean helper scopes

Candidate `a44e8c3f3776e971546a22b8c22818e7877bee4a` admits standard Id input layers around UInt64 and Bool
in general Boolean helper scopes and predicate lets retained inside propositions.
The source grammar records the exact domain and an independent scalar input
certificate. Declared arrow and lambda annotations must match. All function
bodies and arguments are checked, including unused values and functions.

- Source, extraction and source-to-WASM correctness are proved; all 29 audits pass.
- Native Lean/V8 agree on 1,401 inputs across 71 declarations, including 42 ranges.
- 60 prior modules retain identical bytes. publicBoolHelpersInputId shrinks from 1277 to 1219 bytes by using direct scalar extraction.
- New tests pass 105,012 native/IR comparisons, 123,984 invalid-input checks and 1,344 admission controls.
- Prior tests pass 89,280 comparisons, 95,152 invalid-input checks and 960 admission controls.
- The original Id-input probe and nine new fixed probes compile.
- The native corpus contains 1,642 declarations.

[verification.json](verification.json) records commands and source/module hashes.
The [journal](journal.md) preserves failures, fixes and the split dependency build.
A word let surrounding a general Boolean helper also rejects with bare inputs;
that fixed probe is preserved for the next increment. Full-dialect correctness
remains unfinished.
