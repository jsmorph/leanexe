# Inequality and negated comparison conditions

Candidate `95ea4329` adds canonical UInt64 inequality (`≠`) and arbitrary
repeated propositional negation (`¬`) over supported comparisons. The recursive
source model retains each standard decision procedure and both operands. The
recognizer, native semantic lowering, Wasm descriptor recognition, encoding and
typing proofs cover the extended conditions. The instruction emitter is unchanged.

Both final commands exited 0 using pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: complete compiler correctness, exact bytes,
  full module validation and exported execution, with all nine axiom audits.
- `tools/arithmetic-check.js engine`: source admission, reserved exports and
  1,764 matching native Lean/V8 results across all ninety-four declarations.

Nine new scalar fixtures exercise inequality, negation of equality and all
order comparisons, negated Boolean equality/inequality coerced to propositions,
repeated negation, local functions and joined monadic bindings. Three new range
fixtures cover break, continue and step-result branch joins. All 198 focused
native Lean/IR comparisons passed. Custom inequality and negation decision
expressions are rejected. Inputs include equal and unequal operands, zero
divisors, high-bit values, wrapping arithmetic and masked shift counts.

The full engine group was used because the shared comparator affects scalar
expressions and loops. All ninety-four exact modules and native expected results
are retained; verification.json records sizes and SHA-256 hashes. All eighty-two
previously admitted modules are byte-for-byte unchanged: forty-eight range
modules from the preceding checkpoint and thirty-four scalar modules from the
five earlier arithmetic/let/conditional/do/function checkpoints. The latter
identities and paths are recorded in prior-pure-modules.json. The fixed
arithmetic archive and unrelated independent runtime/type-safety suite were not
rebuilt. Affected general proof dependencies, including type validation, passed
using cached imports.

Negation here is Lean's propositional `¬`, including a Boolean comparison
coerced to a proposition. Boolean `!`, compound conditions and Boolean bindings
remain separate language extensions.
