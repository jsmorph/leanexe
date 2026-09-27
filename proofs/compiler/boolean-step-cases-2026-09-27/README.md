# Boolean step-result inspection

Candidate `1b342ce5dad73f35e3b162ef6cb2d1f167b36d2e` admits explicit nondependent ForInStep.casesOn for
Boolean loop-step results. The selected branch receives the payload and determines
the resulting value and exit flag. A done input may yield and continue. Motive
and branch domains, standard Id result annotations and both branches are checked.

- Source totality, extraction and source-to-WASM correctness are proved.
- All nineteen compiler axiom audits pass.
- Native Lean/V8 agree on 1,005 inputs across 52 declarations, including 29 ranges.
- 44 prior modules retain identical bytes; 0 changed.
- New tests pass 18,624 native/IR comparisons and 10,752 invalid-input checks.
- Prior tests pass 95,760 comparisons and 51,936 invalid-input checks.
- Three explicit casesOn probes are restored; four scalar-helper probes remain accepted.
- The native corpus contains 1,623 declarations.

[verification.json](verification.json) records commands and source/module hashes.
The [journal](journal.md) records the primitive and generated-matcher distinction.
Ordinary match through a generated matcher declaration and full-dialect compiler
correctness remain open.
