# Boolean continuations of monadic word loops

Candidate `9c95d8ab4d24ad79f2abcba8789e8a39cd12701b` admits standard Id monadic binding of a word-valued loop
to a Boolean continuation. Exact continuation domains and standard bind evidence
are checked. Input and output may retain standard Id layers. Source evaluation
and the public result theorem preserve the native flag and its zero/one encoding.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 579 inputs across 28 declarations, including twenty ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 32,496 native/IR comparisons, 46,080 invalid-input checks and 2,304 explicit-let controls.
- Prior tests pass 121,416 comparisons, 67,200 invalid-input checks and 4,224 controls.
- The full native corpus contains 1126 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The compiler proof ran on `d489bfd9933e057f79ab1df78ab0fbac9397f3b2`. The subsequent commit only renamed
ten new native fixtures and their registrations to avoid prior test names;
compiler and proof sources are identical.
The [journal](journal.md) and logs retain failed fixture attempts. The preserved
helper-tail fixture identifies unsupported Pure.pure-wrapped helper-let bodies.
Validation uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local
runner. Setup before Boolean loops, broader helper/proposition bodies and
full-dialect compiler correctness remain open.
