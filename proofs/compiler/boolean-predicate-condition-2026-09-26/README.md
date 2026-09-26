# Direct scalar Boolean conditions

Candidate `86df3811d50a31545251f081cde84524fc40f90e` admits Bool-input predicate calls in scalar conditions.
Ordinary and dependent branches support truth tests and Boolean Eq/Ne conditions,
including captures, nested calls and scalar expressions inside loops. Both
branches and every condition input are checked.

- The general source-to-WASM theorem and eighteen axiom audits pass.
- Native Lean/V8 agree on 519 inputs across 28 declarations, including fourteen ranges.
- Eighteen shared modules retain identical bytes.
- Focused tests pass 5,556 native/IR comparisons, 5,844 invalid-input checks and 420 controls.
- Prior tests pass 7,636 comparisons, 5,274 invalid-input checks and 336 controls.
- The full native corpus contains 882 declarations.

[verification.json](verification.json) records revisions, commands, source hashes
and modules. The [journal](journal.md) records proof work and diagnostics. The
proof revision precedes the final admission-test correction; compiler and theorem
sources are identical. Validation uses pinned Lean 4.34.0-rc2, Node 24.13.0 and
the authorized serial local runner.

Direct loop-step conditions, Boolean do binds, direct Boolean helper results and
full-dialect compiler correctness remain subsequent work.
