# Standard numeral instances through constant wrappers

Candidate `422d32d8` accepts the exact standard UInt64 numeral instance
behind unused let binders, lambda/application wrappers and metadata. An independent
source predicate tracks how many arguments are still needed. Its only value
leaf is UInt64.instOfNat for the same numeral, and the production checker must
finish at arity zero. Acceptance and successful-check soundness are proved.
Custom instance values, unknown instance variables, mismatched numerals,
unapplied functions and extra applications are rejected. Source totality, all
four scalar extraction proofs and exact range-count inversion were extended;
loop steps reuse the same scalar path. No emitter or runtime code changed.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: all nine audits, including complete module
  type validation, exact bytes and terminating source-equal exported execution.
- `tools/arithmetic-check.js subset-engine literal-instances`: admission,
  reserved exports and 537 native Lean/V8 comparisons across 30 declarations.

All 208 focused native/IR comparisons pass across eight pure and four range
cases. The original failing captured helper from the preceding Boolean-dependent
increment is included unchanged apart from its name and now passes end to end.
Additional cases cover explicit wrappers, shadowing, proof arguments, overflow,
do-block joins, loop steps, break/continue, bounds and outer helpers. Four
source-level custom-instance rejections, five raw instance rejections and one
metadata acceptance test pass. Explicit wrapper tests use nat_lit to isolate
the instance behavior from the separate Nat numeral expression capability.

The initial explicit fixtures omitted @ on an implicit numeral parameter; the
corrected spelling then exposed Nat OfNat syntax in explicit numeric arguments.
Both failures and the raw elaborated expression are retained. Standard Nat
numeral expressions, including borrowed-type metadata, remain the next increment.
The original reported helper uses normal user numeral syntax and is fully fixed.

All tested modules and expected results are retained with sizes and SHA-256
hashes in verification.json. Eighteen selected preceding modules kept identical
bytes. This focused run checks 30 declarations; the complete corpus contains
379. The last full 259-declaration execution evidence remains in
../extrema-2026-09-25. Cached dependencies were reused; the fixed arithmetic
archive and unrelated runtime suite were not rebuilt. One bounded dependency
build reached its overall time limit after successful modules; smaller remaining
targets completed before the final audits.
