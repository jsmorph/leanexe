# UInt64 bitwise complement

Candidate `efaa5c37` adds the direct UInt64.complement primitive and standard
`~~~` operator. The independent source grammar retains their exact heads and
standard Complement instance. Lowering uses the existing XOR instruction with
the full 64-bit mask; a checked theorem derives its native meaning from
UInt64.xor_neg_one. Scalar acceptance, preservation and invariants carry that
lowering through helpers, comparison operands, monadic code and loop steps.
The range-bound proof explicitly distinguishes complement from literal syntax.
No new backend operator or runtime implementation was needed.

Both final commands exited 0 using pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: complete compiler correctness, exact bytes,
  full module validation and exported execution, with all nine axiom audits.
- `tools/arithmetic-check.js engine`: admission, reserved exports and 3,986
  matching native Lean/V8 results across all 197 declarations.

Eight new pure declarations cover both syntax forms, repeated complement,
combined bitwise/arithmetic operations, nested guards, local functions and
monadic binds/updates. Four range declarations cover break, continue, helpers
around a loop-result binding, direct step functions and complemented interval
bounds near the word limit, including wrapping endpoint expressions and empty
intervals. All 208 focused native Lean/IR comparisons and three rejection tests
passed. Custom Complement instances, unsupported wrapper calls and unsupported
unused helper bodies remain rejected.

All 197 exact modules and native expected results are retained with sizes and
SHA-256 hashes in verification.json. All 185 prior modules retained identical
bytes: 125 range modules and 60 pure scalar modules. The full group was used
because shared scalar extraction changed. General type validation used cached
dependencies; the fixed arithmetic archive and unrelated runtime suite were not
rebuilt.
