# Mixed scalar and loop arms in Boolean conditions

Candidate `c92a568da659752c14148e153311f03ce53b6f51` admits scalar Boolean and loop arms in either order,
including both-scalar conditions and standard Id result annotations. Each arm
first tries scalar extraction, then lazily extracts a loop if needed. Both arms
are checked. Scalar arms use proved zero-iteration plans; the captured condition
selects the same arm throughout execution.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 97,008 native/IR comparisons, 41,472 invalid-input checks and 3,456 wrapper controls.
- Prior tests pass 32,496 comparisons, 29,952 invalid-input checks and 2,304 controls.
- The full native corpus contains 1236 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records proof and execution checks.
Validation uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local
runner. Local continuations containing loops, broader helper and
proposition bodies, and full-dialect compiler correctness remain open.
