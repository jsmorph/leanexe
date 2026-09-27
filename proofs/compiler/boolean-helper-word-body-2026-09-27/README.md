# General predicate bodies before scalar word continuations

Candidate `46940b375f298d760f90163ea80d0ecfe4d655d4` admits nested helpers, wrappers and choices in predicate
bodies followed by scalar word-valued code. The checked body conversion retains
Boolean encoding, captures and exact helper annotations. Unused bodies are
validated. Proposition lets use the same checked scalar path.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 993 inputs across 54 declarations, including 25 ranges.
- 44 prior modules retain identical bytes; 0 changed.
- New tests pass 88,884 comparisons, 95,152 invalid-input checks and 1,728 controls.
- Prior tests pass 66,888 comparisons, 48,400 invalid-input checks and 2,048 controls.
- Ten new probes and the original nested proposition-let probe pass unchanged.
- Three prior converted-helper controls still pass; the Id-input probe remains rejected.
- The full native corpus contains 1517 declarations.

[verification.json](verification.json) records commands, source/module hashes and
prior module comparisons. The [journal](journal.md) records the raw-body proof
change and generated induction cases. The next loop probes admit three forms
through existing scalar paths and reject a Boolean-input helper before break and
two outer-loop helper forms. Those dedicated step/outer parsers, Id inputs,
composition of loops, retained instances, broader signatures and full-dialect
compiler correctness remain open.
