# Boolean negation in conditional guards

Candidate `3c620953` adds Boolean `!` over standard UInt64 equality/inequality
comparisons, including repeated `!` and propositional `¬` around those guards.
An independent Boolean syntax and native semantic model retain the actual
Bool.not/BEq expressions. Recognition checks the exact standard instances and
decision evidence. The polarity theorem lowers repeated negation to equality
or its negation while preserving both operand evaluations. Encoding and full
module type validation are proved through the existing instruction emitter.

Both final commands exited 0 using pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: complete compiler correctness, exact bytes,
  full module validation and exported execution, with all nine axiom audits.
- `tools/arithmetic-check.js engine`: admission, reserved exports and 3,298
  matching native Lean/V8 results across all 165 declarations.

Eight new pure declarations cover equality/inequality, repeated negations,
computed comparison operands, nested branches, local functions, monadic binds,
updates and propositional negation. Four range declarations cover break,
continue, result joins and binary step-result functions. All 208 focused
native Lean/IR comparisons and three rejection tests passed. Custom BEq,
custom decision evidence and unsupported Boolean helper calls remain rejected.
The initial negative fixture had a Bool/Prop elaboration mismatch; its failed
log is retained in native-ir-initial.log. The corrected fixture uses an explicit
Bool equality, and the complete final test command exited successfully.

All 165 exact modules and native expected results are retained with sizes and
SHA-256 hashes in verification.json. All 153 prior modules retained identical
bytes: 101 range modules and 52 pure scalar modules. The full group was used
because shared comparison extraction changed. The fixed arithmetic archive
and unrelated runtime suite were not rebuilt; the general proof used cached
dependencies. Compound conditions and general Boolean values remain separate
capabilities.
