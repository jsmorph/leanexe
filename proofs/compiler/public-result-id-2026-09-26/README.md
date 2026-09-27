# Id annotations on public scalar results

Candidate `3a708b4978fc40314d08140eaee9770bef8b74b0` admits standard Id layers around public UInt64 and Bool
result types, including intervening metadata. Signature recognition requires a
scalar base result; Id around function types and malformed annotations are
rejected. Result encodings and complete body checks are preserved.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 33,204 native/IR comparisons, 20,352 invalid-input checks and 1,536 controls.
- Prior tests pass 93,130 comparisons, 67,023 invalid-input checks and 3,456 controls.
- The full native corpus contains 1076 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) and logs record proof and validation results.
Validation uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local
runner. Public Boolean parameters and loop results, retained instances, broader
signatures and full-dialect compiler correctness remain subsequent work.
