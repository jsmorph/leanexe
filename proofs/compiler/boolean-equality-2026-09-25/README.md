# Boolean equality and inequality

Candidate `67876321` supports Bool-valued `==` and `!=`, including explicit
BEq.beq and bne calls using the exact standard Bool equality instance. Both
sides may contain admitted Boolean literals, saved flags, comparisons,
decisions, junctions, choices, equality/inequality and repeated negation.
The recursive BooleanLocal form preserves typed lexical references and every
scalar operand. Shared lowering compares the canonical zero/one words with a
proved native Boolean meaning and invariant preservation. Scalar, step and
outer-loop semantics and compiler proofs reuse their existing interfaces.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: all nine audits, including complete module
  type validation, exact bytes and terminating source-equal exported execution.
- `tools/arithmetic-check.js subset-engine boolean-equality`: admission,
  reserved exports and 623 native Lean/V8 comparisons across 34 declarations.

All 304 focused native/IR comparisons, four source rejections and sixteen raw
equality rejections passed on the first fixture run. Cases cover operators,
explicit calls, literal truth cases, saved flags, nested equalities/choices,
repeated negation, ordinary/dependent conditions, helper captures, conditional
Id binds, loop break/continue, joined updates, strided bounds, step-result
helpers and post-loop computation. Custom/unknown/mismatched instances, wrong
operand types and universe levels, and unsupported operands are rejected.
Both inputs are checked even when unused. The preceding Boolean-conversion
fixture passes unchanged: 304 comparisons and seventeen rejection checks.

Five original inspected declarations rejected before this increment and now
accept unchanged; their source and both syntax logs are retained. This adds
Bool-valued equality, with public arguments/results still UInt64. Propositional
Boolean equality involving saved flags remains a separate extension. No
emitter/runtime or scalar/loop dispatch changes were needed. Eighteen selected
preceding modules have identical bytes. Emitted modules, native results, sizes
and SHA-256 hashes are retained. This focused run covers 34 declarations; the
complete corpus contains 504. The last full 259-declaration execution evidence
remains in ../extrema-2026-09-25. Cached dependencies, the fixed arithmetic
archive and unrelated runtime suite were reused.
