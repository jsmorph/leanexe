# Boolean loop accumulators

Candidate `d357e3a3d8f31cd56ff12f4efb73379a5c47c2c6` admits bounded ranges with Boolean state, checked
choices, scalar lets, early exits, continue, positive literal strides and
captured scalar helpers. Public Boolean inputs use the existing i64 decoding;
Boolean results are zero or one. Word continuations may consume the loop result.

- Source totality, extraction and source-to-WASM correctness are proved.
- Nineteen compiler axiom audits and two native iteration audits pass.
- Native Lean/V8 agree on 1,101 inputs across 56 declarations, including 33 ranges.
- 44 prior modules retain identical bytes; 0 changed.
- New tests pass 14,112 native/IR comparisons and 6,912 invalid-input checks.
- Prior tests pass 47,856 comparisons, 25,488 invalid-input checks and 0 controls.
- Nine previously rejected fixed probes now compile; twelve prior controls remain accepted.
- The native corpus contains 1,565 declarations.

[verification.json](verification.json) records commands and source/module hashes.
The [journal](journal.md) preserves proof development, test failures and repairs.
Boolean step monadic binds and step-returning helpers, retained Id inputs in
converted helper scopes, multiple loops and full-dialect correctness remain open.
