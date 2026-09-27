# Boolean calls as word and step helper arguments

Candidate `860d84032a3597e6582bfcfc3c356c7189fcbacb` compiles complete Boolean arguments through the existing
checked conversion path. Word- and step-returning Bool-input helpers accept
nested calls, choices, decisions, bindings and Id computations. Source argument
evaluation proves its Boolean encoding before applying the helper.

- The general source-to-WASM theorem and eighteen axiom audits pass.
- Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 57,012 native/IR comparisons, 48,384 invalid-input checks and 2,688 controls.
- Prior tests pass 63,666 comparisons, 33,359 invalid-input checks and 1,920 controls.
- The full native corpus contains 1056 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) and logs preserve proof attempts and validation results.
Validation uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local
runner. Public Boolean results, retained instances, broader signatures and
full-dialect compiler correctness remain subsequent work.
