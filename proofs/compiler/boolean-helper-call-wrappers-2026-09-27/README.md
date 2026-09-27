# Wrapped calls to local Boolean helpers

Candidate `52ea98bfe3406fd32da56a837c19ab5260a05566` retains standard Id run/pure and metadata wrappers around
named Boolean helper calls, including pure introduced by return. Exact source
syntax, helper annotations and wrapper instances are checked. Arguments cannot
refer recursively to the introduced helper. The saved loop-bind capture fixture
passes unchanged; scalar expressions, conditions, captures and loop steps are
also exercised.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 549 inputs across 28 declarations, including seventeen ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 14,292 native/IR comparisons, 10,080 invalid-input checks and 2,016 controls.
- Prior tests and the restored fixture pass 20,176 comparisons, 12,880 invalid-input checks and 1,280 controls.
- The full native corpus contains 1387 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records proof and execution checks. Validation uses
pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.
Broader Boolean propositions and helper compositions, general local loop-function
application, multiple loops, retained instances, broader signatures and full-dialect
correctness remain open.
