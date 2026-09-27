# Propositional choices with Boolean helper branches

Candidate `0c20ed1959b63ffbb68ffda06197d9e3b6f8ff99` admits Boolean-valued choices over existing supported
propositional guards, with recursively checked helper operands and Boolean
branches. Guard semantics, evidence, result annotations and dependent binders
are preserved. Source execution evaluates the selected branch; compilation
checks both. Guards cover UInt64 comparisons, negation, compound propositions
and word/Boolean proposition lets.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 993 inputs across 54 declarations, including 25 ranges.
- 44 prior modules retain identical bytes; 0 changed.
- New tests pass 37,812 comparisons, 51,072 invalid-input checks and 768 controls.
- Prior tests pass 41,140 comparisons, 45,056 invalid-input checks and 1,024 controls.
- Three original rejected probes now pass; two positive controls still pass.
- The full native corpus contains 1477 declarations.

The unchanged extended probe still rejects direct Boolean relation/equality-to-false
conditions and a helper moved by elaboration into a function-typed proposition let.
The initial native fixture hit the latter gap. Its replacement cases use explicit
Boolean-to-word guard operands; both fixtures and the diagnostic are retained.
This increment does not claim that the function-typed proposition-let gap is fixed.

[verification.json](verification.json) records commands, source/module hashes and
prior module comparisons. The [journal](journal.md) explains parser corrections,
the deferred guard case and the rejected wrapped-decision size approach. Draft
files ending in .lean.txt are unverified attempts, not checked proof modules.
Direct Boolean relation conditions, function-typed proposition lets, broader
helper bodies and Id inputs, multiple loops, retained instances, broader signatures
and full-dialect compiler correctness remain open.
