# Compound guard decision equivalence

Candidate `c602f7944ac2fdb34daee2a3b78827db93df0466` accepts proposition guard trees containing comparison
leaves whose condition and decision operands differ by proved standard arithmetic
annotations. The source relation `GuardDecision` composes the independent
`Reannotates` relation through conjunction, disjunction and negation. It retains
the complete enclosing propositions and standard decision instances. Ordinary
scalar and loop-step branches share the existing guard lowering.

Validation uses pinned Lean 4.34.0-rc2 and Node 24.13.0 with authorized serial
local execution through `tools/leanrun`:

- `tools/arithmetic-check.js proof`: the general source-to-WASM theorem and all
  fourteen axiom audits pass, including exact decoding, module validation and
  execution to the source result in the pinned Wasm model.
- `tools/arithmetic-check.js subset-engine guard-decision`: 903 native Lean/V8
  comparisons pass across 54 declarations, including sixteen range declarations.
- All 46 modules from the preceding comparison increment retain identical bytes.
  The full native fixture contains 694 declarations.
- New focused tests pass 468 native/IR comparisons and 144 invalid-input tests,
  covering nested and negated guards, literals, Boolean subguards, helpers, Id
  actions, loop exits, wrong connective instances and mismatched child evidence.
- Previous atomic annotation tests pass 1,550 comparisons and 990 rejections.

The [journal](journal.md) records proof construction and retained failures.
[verification.json](verification.json) records the candidate, commands, source
hashes, exact modules and execution scope. The initial aggregate source build
reached its 60-second limit; the remaining step and function targets were built
separately before the complete proof and execution gates passed.

Differently annotated operands in dependent branch and saved-decision evidence
remain subsequent work. Boolean compound subguards retain their exact standard
evidence. Full LeanExe dialect compiler correctness remains unfinished.
