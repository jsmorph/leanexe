# Comparison operand equivalence

Candidate `aadf243efb1b872f5d41f3b205ef464f0b0a7539` accepts standard arithmetic operands whose type
annotations differ between an ordinary comparison's condition and decision
expression. `Reannotates.eval_iff` independently proves preservation of source
evaluation. The recognizer has soundness and acceptance proofs, and the complete
standard decision expression is checked. The extension applies to ordinary
scalar and loop-step branches, including local helpers and Id actions.

Validation uses pinned Lean 4.34.0-rc2 and Node 24.13.0 with authorized serial
local execution through `tools/leanrun`:

- The general source-to-WASM theorem and all twelve axiom audits pass. The theorem
  covers exact emitted bytes, module decoding and validation, export lookup,
  and execution to the source result in the pinned Wasm model.
- Native Lean and V8 agree on 771 inputs across 46 declarations, including
  fourteen range declarations. All 35 previously checked modules retain
  identical bytes. The full native corpus has 686 declarations.
- Focused source and syntax tests pass 2,066 native/IR comparisons and 1,204
  invalid-input tests. These cover all ten arithmetic operations, all six
  propositional comparisons, Boolean equality/inequality, nested negation,
  local helpers, Id actions, numeral instances and metadata.
- The original `rangeIdComparisonEvidenceAnnotations` program compiles unchanged
  and agrees with native Lean in both IR and emitted-Wasm execution.

The merge from main required a proof translation correction: structured branch
result types are retained consistently. The initial failure, focused translation
check and final general proof are preserved. The first execution check found
missing new names in its checked corpus list; the corrected list was checked
against the already-built modules without recompiling them.

The [journal](journal.md) records proof development and retained failures.
[verification.json](verification.json) identifies the candidate, commands,
source hashes, exact modules and execution scope. This directory also contains
the test sources, native expected outputs and successful proof/execution logs.

Operand equivalence within compound guard evidence, dependent branches and saved
decisions remains subsequent work. This is a general theorem for the admitted
scalar language; it does not establish compiler correctness for the full
LeanExe dialect.
