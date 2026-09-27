# General predicate bodies in loop-step bindings

Candidate `920d03cfc2e3b6857a251d9cbad27a8fb72871fc` admits nested helpers, wrappers and choices in predicate
bodies declared inside loop steps. The checked scalar conversion preserves
Boolean encoding and captures. Every body is validated, including unused bodies.
The step proof preserves both the resulting word and the loop exit flag.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 1,053 inputs across 54 declarations, including 31 ranges.
- 44 prior modules retain identical bytes; 0 changed.
- New tests pass 32,496 comparisons, 19,584 invalid-input checks and 1,152 controls.
- Prior tests pass 101,136 comparisons, 94,240 invalid-input checks and 1,104 controls.
- Ten new probes and the original helper-before-break probe pass unchanged.
- Three prior loop controls still pass; two outer-loop probes remain rejected.
- The full native corpus contains 1527 declarations.

[verification.json](verification.json) records commands, source/module hashes and
prior module comparisons. The [journal](journal.md) records the raw-body proof
change and the corrected induction diagnostic import. Ten further outer-prefix
probes are retained as rejected inputs for the next capability. Outer-loop
helper bodies, Id inputs in converted scopes, composition of loops, retained
instances, broader signatures and full-dialect compiler correctness remain open.
