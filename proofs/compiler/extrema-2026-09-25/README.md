# UInt64 minimum and maximum

Candidate `93471a4b` admits standard UInt64 min/max with their exact Min/Max
instances. The independent source grammar records their native meanings.
Checked lowering uses unsigned less-than-or-equal followed by selection,
matching the existing dialect implementation. Scalar totality, acceptance,
correctness and invariants carry the new operations through the public function,
loop-step and range-bound interfaces without backend or runtime changes.

Both operands are checked and evaluated in the source semantics. Emitted code
may evaluate a selected operand again; the operands are pure and total, so this
preserves results. Custom instances are rejected, including in unused bodies.

Both final commands exited 0 using pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: complete compiler correctness, exact bytes,
  full module validation and exported execution, with all nine axiom audits.
- `tools/arithmetic-check.js engine`: admission, reserved exports and 5,074
  matching native Lean/V8 results across all 259 declarations.

Eight new pure declarations cover order, equal inputs, high bits, nested extrema,
clamps, lexical captures, binary local functions, monadic joins, mixed guards,
zero divisors and wrapping arithmetic. Four range declarations cover computed
bounds, break, continue, near-limit short intervals, outer result bindings and
binary step helpers. All 208 focused native Lean/IR comparisons and three
rejection tests passed. The near-limit fixture bounds its start by 2^64-3 and
its distance by two, so the test exercises high indices without enormous loops.

All 259 exact modules and native expected results are retained with sizes and
SHA-256 hashes in verification.json. All 247 prior modules retained identical
bytes. General type validation used cached dependencies; the fixed arithmetic
archive and unrelated runtime suite were not rebuilt.
