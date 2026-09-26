# Nested propositional guards

Candidate `943588a1` adds nested propositional conjunction and disjunction over
the admitted UInt64 comparisons. The separate guard syntax retains every scalar
operand, and the recognizer checks the entire tree's exact standard decision
evidence. Its compiler accepts precisely the checked guard shape, preserves
native Boolean results, and preserves the existing scalar invariants.

The source grammar and public extractor carry compound guards through both
ordinary scalar conditionals and paired value/exit loop-step results. Both
branches and every operand are checked, including unused helper bodies.
Lowering materializes Boolean words, combines them with the existing AND/OR
operations, then compares the result with one. All admitted operands are pure
and total, so evaluating both sides preserves results. No backend operators or
runtime implementation changed. Atomic comparisons retain their old path.

Both final commands exited 0 using pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: complete compiler correctness, exact bytes,
  full module validation and exported execution, with all nine axiom audits.
- `tools/arithmetic-check.js engine`: admission, reserved exports and 4,242
  matching native Lean/V8 results across all 211 declarations.

Eight new pure declarations cover both truth tables, mixed nested connectives,
negated comparison leaves, zero divisors, captures, binary local functions,
monadic joins and nested conditional operands. Six range declarations cover
break, continue, mutable branch updates, helpers surrounding loop-result lets,
binary step helpers and result-taking continuations. All 256 focused native
Lean/IR comparisons and three rejection tests passed. Custom decision evidence,
unsupported scalar operands and unsupported unused helper bodies remain rejected.

All 211 exact modules and native expected results are retained with sizes and
SHA-256 hashes in verification.json. All 197 prior modules retained identical
bytes. The full group was used because shared scalar extraction changed.
General type validation used cached dependencies; the fixed arithmetic archive
and unrelated runtime suite were not rebuilt. Boolean &&/||, negation of an
entire compound and general Boolean values remain later coverage increments.
