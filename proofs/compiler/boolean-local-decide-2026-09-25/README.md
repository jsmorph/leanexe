# Decisions on Boolean equality and saved flags

Candidate `25a0d3b5e66ab4e9fd392f1c4bb21a2107fc0d8a` supports explicit decide and implicit Prop-to-Bool
conversions for Boolean `=` and `≠`, including truth coercions such as
`decide flag` and `decide (flag = true)`. Both inputs may contain admitted
Boolean expressions, saved flags, choices and nested decisions. The recursive
source form retains the exact Eq/Ne condition and complete standard decision
evidence. Its native decide meaning is proved equal to Boolean equality, and
it shares the equality lowering and proofs. The prior closed decision form
now uses PropositionGuard; Boolean truth decisions use the recursive relation
path. Non-Boolean closed guards retain their existing lowering. No emitter or
runtime changes were needed.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: all nine audits, including complete module
  type validation, exact bytes and terminating source-equal exported execution.
- `tools/arithmetic-check.js subset-engine boolean-local-decide`: admission,
  reserved exports and 623 native Lean/V8 comparisons across 34 declarations.

The first focused fixture run passed all 304 native/IR comparisons, four
source rejection tests and thirty-two raw decision rejection tests. Cases cover
Eq/Ne and truth coercions, implicit conversions, literal truth cases, nested
decisions, Boolean-result choices using already admitted guards, negation,
helper captures, conditional Id binds, ordinary/dependent conditions, joined
loop updates, continue/break, strided bounds, step-result helpers and before/
after-loop code. Unknown, custom or mismatched evidence, wrong input kinds and
universe levels, unsupported operands and inactive/unused Boolean branches
are rejected. The preceding proposition-guard fixture passes unchanged with
304 comparisons and 44 rejection tests; the earlier closed-decide fixture also
passes unchanged with 304 comparisons and twelve rejections.

Five original inspected declarations now compile unchanged. The two retained
leading-negation cases from the preceding increment also compile unchanged and
pass native/IR and actual compiler/V8 execution checks under new declaration
names. Their bodies were compared mechanically across the original source,
focused fixture, admission fixture and native result fixture. Exact inspected
source and before/after logs are retained. Initial failure evidence remains in
../boolean-proposition-2026-09-25.

Boolean-result choices directly guarded by saved-flag propositions, broader
propositional combinations, Boolean-returning helpers and Boolean public ABI
remain later capabilities. Eighteen selected preceding modules have identical
bytes. Boolean truth decisions now share relation lowering; byte identity is
claimed only for those eighteen checked modules. Emitted modules, native results,
sizes and SHA-256 hashes are retained. The full corpus has 536 declarations;
this was a focused 34-declaration execution run. The last full 259-declaration
execution evidence remains in ../extrema-2026-09-25. Cached dependencies, the
fixed arithmetic archive and unrelated runtime suite were reused.
