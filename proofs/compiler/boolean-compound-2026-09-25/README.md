# Boolean compound guards

Candidate `f55d3440` adds Boolean && and || over standard UInt64 Boolean
comparisons, with repeated ! at any nesting level. The independent BooleanGuard
source tree retains exact Bool.and, Bool.or, Bool.not and comparison syntax.
Its conversion to the shared guard representation is proved to preserve every
scalar operand and native Boolean result. The common CompoundGuard interface
now distinguishes propositional and Boolean source forms while retaining the
existing public scalar and loop-step source rules and compiler proofs.

The recognizer checks the entire standard Bool-equals-true decision expression.
Both branches and all operands are checked. Lowering reuses Boolean-word AND/OR
and zero/one comparisons; no backend or runtime implementation changed.

Both final commands exited 0 using pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: complete compiler correctness, exact bytes,
  full module validation and exported execution, with all nine axiom audits.
- `tools/arithmetic-check.js engine`: admission, reserved exports and 4,658
  matching native Lean/V8 results across all 235 declarations.

Eight new pure declarations cover both truth tables, repeated negation, nested
Boolean groups, zero divisors, captures, binary local functions, monadic joins
and conditional operands. Four range declarations cover break, continue, mutable
branch updates, binary step helpers and result-taking continuations. All 208
focused native Lean/IR comparisons and three rejection tests passed. Custom BEq
instances, custom decision evidence, and custom instances in unused helper
bodies remain rejected.

All 235 exact modules and native expected results are retained with sizes and
SHA-256 hashes in verification.json. All 223 prior modules retained identical
bytes. General type validation used cached dependencies; the fixed arithmetic
archive and unrelated runtime suite were not rebuilt. Combining a compound
Boolean guard with surrounding propositional connectives, plus general Boolean
variables/results, remain later increments.
