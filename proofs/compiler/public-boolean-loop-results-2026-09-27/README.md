# Boolean results computed from word-valued loops

Candidate `b98b9c2766cda7e27682b62508b6b8b0ad74d719` admits an explicit UInt64 let binding whose value is a
checked loop and whose body computes a Boolean. Standard Boolean Id run/pure
wrappers and metadata may surround the binding. The independent source semantics
return a Bool, and the public result theorem proves its zero/one encoding.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 559 inputs across 28 declarations, including eighteen ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 16,368 native/IR comparisons and 13,824 invalid-input checks.
- Prior tests pass 182,424 comparisons, 92,160 invalid-input checks and 6,816 controls.
- The full native corpus contains 1116 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) and logs retain failed proof/test attempts and corrections.
Validation uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local
runner. General Boolean-result monadic loop sequencing, setup before Boolean
loops, broader helper/proposition bodies and full-dialect correctness remain open.
