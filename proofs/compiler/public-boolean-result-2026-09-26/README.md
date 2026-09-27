# Public Boolean results

Candidate `c27bdf7b7e6e3ceb97bd42349b67675a64e943de` admits public Bool results with UInt64 arguments.
Boolean bodies use the existing checked conversion and i64 export ABI. The
source application and explicit result theorem prove false=0 and true=1 for
every argument list of the declared arity. UInt64 loop results retain their
existing compilation paths.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 469 inputs across 28 declarations, including nine ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 16,652 native/IR comparisons, 7,872 invalid-input checks and 768 controls.
- Prior tests pass 120,678 comparisons, 81,743 invalid-input checks and 4,608 controls.
- The full native corpus contains 1066 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) and logs record proof and validation results.
Validation uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local
runner. Public Id annotations, Boolean parameters and loop results, broader
signatures and full-dialect compiler correctness remain subsequent work.
