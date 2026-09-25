# Bool-valued decide conversions

Candidate `c06588b6` supports explicit `decide` and implicit Prop-to-Bool
conversions over the existing closed guard grammar: UInt64 comparisons, True,
False, negation, conjunction, disjunction and closed Boolean guards. Exact
standard decision evidence is checked before accepting Decidable.decide. The
BooleanLocal decision form records source syntax, operands and native meaning;
shared lowering reuses the proved guard compiler. Repeated Boolean negation,
junctions, choices, captures, Boolean helper arguments and Id actions compose
through the existing scalar and loop interfaces. All operands are checked,
including those under inactive or unused decisions.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: all nine audits, including complete module
  type validation, exact bytes and terminating source-equal exported execution.
- `tools/arithmetic-check.js subset-engine decide`: admission, reserved exports
  and 623 native Lean/V8 comparisons across 34 declarations.

All 304 focused native/IR comparisons, four source rejections and eight raw
parser rejections passed on the first execution run. Cases cover all six UInt64
propositional comparisons, implicit conversions, compound guards, closed Boolean
conditions, nested choices, repeated negation, capture/shadowing, dependent
branches, conditional Boolean binds, unused values, break/continue, joined
updates, strided bounds, step-result helpers and pre/post loop computations.
Wrong universe levels, custom or mismatched decision evidence and unsupported
operands remain rejected. The preceding Boolean-function fixture passes unchanged:
328 comparisons and sixteen rejection checks.

Five original inspected examples rejected before this increment and now accept
unchanged, including the implicit conversion in the loop-stop expression found
by the preceding increment. Both syntax logs and their source are retained.
No emitter/runtime code changed. Eighteen selected preceding modules have
identical bytes; all emitted modules, native results, sizes and SHA-256 hashes
are retained. This focused run covers 34 declarations; the full corpus contains
472. The last full 259-declaration execution evidence remains in
../extrema-2026-09-25. Cached dependencies were reused; the fixed arithmetic
archive and unrelated runtime suite were not rebuilt.

Decisions whose propositions directly mention saved Boolean locals, Boolean
public parameters/results, Boolean-returning helpers, mixed Bool/word parameter
lists and loops inside helpers remain separate capabilities.
