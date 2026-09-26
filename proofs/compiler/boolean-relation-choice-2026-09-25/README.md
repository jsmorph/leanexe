# Boolean results selected by Boolean equality and inequality

Candidate `2b75649b623526b4c0ddcf088bd87595ca238e23` supports Boolean-result choices guarded directly by Boolean
`=` and `≠`, including conditions containing saved flags. Both inputs and both
result branches may contain admitted Boolean expressions, choices and decisions.
The source representation retains exact Eq/Ne syntax and complete standard
decision evidence. Native choice uses the proved decision meaning; extraction
shares Boolean equality and selection lowering. Parser acceptance,
reconstruction, operand-size, typed-variable, totality, semantic and invariant
proofs cover all four recursive children.

Ordinary `if flag then … else …` choices have a literal true right operand.
A checked literal test and a proved lowering specialization preserve their
original compiled condition, without adding a comparison with true. All other
relations compare their two checked zero/one Boolean values. Every operand and
branch is checked, including unused or inactive results. No emitter or runtime
changes were needed.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: all nine audits, including complete module
  type validation, exact bytes and terminating source-equal exported execution.
- `tools/arithmetic-check.js subset-engine boolean-relation-choice`: admission,
  reserved exports and 623 native Lean/V8 comparisons across 34 declarations.

The first focused fixture run passed all 304 native/IR comparisons, four source
rejection tests and forty raw choice rejection tests. Cases cover Eq/Ne, literal
truth cases, ordinary truth-choice equivalence, nested choices/decisions,
negation, captures, Id binds, ordinary/dependent scalar and step conditions,
joined loop updates, continue/break, strided bounds, step-result helpers and
before/after-loop code. Unknown, custom and mismatched evidence, incorrect
operand/binding/result types, wrong universe levels and unsupported inactive
branches are rejected. Both the preceding Boolean-local-decide fixture and the
original Boolean-choice fixture pass unchanged: each has 304 comparisons, with
36 and twelve rejection checks respectively.

All five original inspected examples now compile unchanged and their bodies
match the focused, admission and native-result fixtures. The exact inspected
source and before/after syntax logs are retained. This adds ordinary Boolean
results selected by Eq/Ne; dependent Boolean-result choices, broader saved-flag
propositions, Boolean-returning helpers and Boolean public ABI remain later
capabilities. Eighteen selected preceding modules have identical bytes. Emitted
modules, native results, sizes and SHA-256 hashes are retained. The complete
corpus contains 552 declarations; this was a focused 34-declaration execution
run. The last full 259-declaration execution evidence remains in
../extrema-2026-09-25. Cached dependencies, the fixed arithmetic archive and
unrelated runtime suite were reused.
