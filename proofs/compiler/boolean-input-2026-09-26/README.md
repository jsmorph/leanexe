# Id annotations on Bool-input local helpers

Candidate `67cdc30b3558c41fa7f02904dd6be80de3e126df` admits matching standard Id annotations on Boolean
helper inputs. The source rule removes one layer at a time, preserving helper
results, bodies, captures and uses for recursive checking. Existing Bool-, UInt64-
and ForInStep UInt64-returning helpers retain their supported scopes.

- The general source-to-WASM theorem and eighteen axiom audits pass.
- Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 19,124 native/IR comparisons and 10,752 invalid-input checks.
- Prior tests pass 82,258 comparisons, 48,911 invalid-input checks and 2,160 controls.
- The full native corpus contains 1046 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) and logs preserve proof attempts and validation results.
Validation uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local
runner. Broader helper arguments, retained instances, signatures and full-dialect
compiler correctness remain subsequent work.
