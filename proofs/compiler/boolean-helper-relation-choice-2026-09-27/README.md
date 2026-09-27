# Boolean relation choices with general helper scopes

Candidate `32932d289287a562de2407b7167274d7294d5d51` admits Boolean-valued choices with direct Boolean Eq/Ne
conditions containing recursively supported helper scopes. Both operands and both
branches are checked. Standard evidence, Bool/Id result annotations and dependent
proof binders are preserved. Equality to true keeps the existing Boolean-truth
path; inequality and equality to false use the relation path. Source execution
evaluates only the selected branch.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 993 inputs across 54 declarations, including 25 ranges.
- 44 prior modules retain identical bytes; 0 changed.
- New tests pass 62,900 comparisons, 97,920 invalid-input checks and 1,280 controls.
- Prior tests pass 53,684 comparisons, 62,080 invalid-input checks and 1,280 controls.
- Ten new probes and the original two relation probes pass unchanged.
- Five previous positive controls still pass.
- The full native corpus contains 1487 declarations.

[verification.json](verification.json) records commands, source/module hashes and
prior module comparisons. The [journal](journal.md) explains the parser and branch
proof corrections. The unchanged compound probe still exposes a function binding
inside a proposition. That case, broader helper bodies and Id inputs, multiple
loops, retained instances, broader signatures and full-dialect compiler
correctness remain open.
