# Boolean-valued conditionals over propositional guards

Candidate `30d47e67` supports Boolean results selected by the existing
closed propositional guards: all six UInt64 comparisons (=, ≠, <, ≤, >, ≥),
True/False, negation, conjunction and disjunction, including supported closed
Boolean comparison/literal leaves. Both result arms may use saved flags,
Boolean or propositional choices, negation and junctions. These choices work
in ordinary lets, standard Id action leaves, captured helper bodies, loop
steps and computations surrounding loops.

The independent PropositionGuard grammar identifies propositional outer syntax
and preserves exact condition/decision expressions. Its parser has acceptance,
reconstruction and size proofs. A separation theorem keeps direct Boolean
coercions on the preceding Boolean-choice path. BooleanLocal carries the new
choice form through source syntax, operands, variables and native meaning.
Shared lowering reuses the existing guard and word-choice theorems. Every
condition operand and both arms are checked. Scalar, step and outer-loop
semantics, totality and extraction proofs reuse these interfaces.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: all nine audits, including complete module
  type validation, exact bytes and terminating source-equal exported execution.
- `tools/arithmetic-check.js subset-engine proposition-choice`: admission,
  reserved exports and 623 native Lean/V8 comparisons across 34 declarations.

All 304 focused native/IR comparisons pass across eight pure and eight range
cases. Cases cover each comparison, propositional literals and compound trees,
mixed Boolean/propositional choice nesting, repeated negation, shadowing,
helper captures, dependent outer conditions, joined do updates, Boolean binds,
unused values, break/continue, strided bounds and pre/post loop computations.
Four source rejections and eight raw choice rejections cover unsupported
inactive or unused arms, custom/mismatched decision evidence and wrong result
or arm types. The preceding Boolean-choice tests pass unchanged: another 304
native/IR comparisons and twelve rejection checks. Both focused test files
passed on their first execution run for this increment.

Propositional combinations containing saved flags and conditional Id actions
remain separate capabilities. No emitter/runtime code changed. All selected
modules, expected results and logs are retained with sizes and SHA-256 hashes
in verification.json. Eighteen selected preceding modules kept identical bytes.
This focused run checks 34 declarations; the complete corpus contains 439.
The last full 259-declaration execution evidence remains in
../extrema-2026-09-25. Cached dependencies were reused with bounded affected
builds. The fixed arithmetic archive and unrelated runtime suite were not rebuilt.
