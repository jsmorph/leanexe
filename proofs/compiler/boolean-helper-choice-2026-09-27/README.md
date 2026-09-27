# Boolean-valued choices containing helper scopes

Candidate `401f35f70e0a6f4130b212901ac896a0ca0f5559` admits Boolean-valued conditionals with helper scopes in
the Boolean condition or either branch. Exact standard truth evidence, Bool/Id
result annotations and dependent proof binders are checked. Source execution
evaluates the selected branch; compilation checks both. Scalar expressions,
word-valued conditions and loop exits use the same checked Boolean conversion.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 993 inputs across 54 declarations, including 25 ranges.
- 44 prior modules retain identical bytes; 0 changed.
- New tests pass 25,268 comparisons, 34,048 invalid-input checks and 512 controls.
- Prior tests pass 53,684 comparisons, 56,320 invalid-input checks and 1,280 controls.
- Ten original probes pass unchanged.
- The full native corpus contains 1467 declarations.

[verification.json](verification.json) records commands, source/module hashes and
prior module comparisons. The [journal](journal.md) explains the proof. Broader
propositional conditions, helper bodies and Id inputs, multiple loops, retained
instances, broader signatures and full-dialect compiler correctness remain open.
