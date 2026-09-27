# Two-argument local scalar functions

Candidate `7dcd290c` adds local functions with two UInt64 arguments and UInt64
or Id UInt64 results. A distinct binding kind preserves both argument values and
the lexical environment. The compiler checks all function bodies, including
unused functions, and substitutes both compiled arguments in source order.
The same bindings are available in ordinary scalar expressions and in helpers
defined inside loop steps. The instruction emitter is unchanged.

Both final commands exited 0 using pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: complete compiler correctness, exact bytes,
  full module validation and exported execution, with all nine axiom audits.
- `tools/arithmetic-check.js engine`: admission, reserved exports and 2,850
  matching native Lean/V8 results across all 143 declarations.

Nine new pure declarations cover argument order, captures and shadowing,
chained and nested functions, unused bodies, Id results, conditionals and
computed arguments. Six new range declarations cover indexed helpers,
accumulator capture across updates, nested helpers, monadic computations,
break/continue and unused functions. All 270 focused native Lean/IR comparisons
passed, with six rejection tests for unsupported unused bodies, excess/wrong
domains and partial applications. The earlier ordinary/loop binary-function
admission rejections are now explicit accepted fixtures.

All 143 exact modules and native expected results are retained with sizes and
SHA-256 hashes in verification.json. All 128 prior modules retained identical
bytes: 85 range modules from the stride checkpoint and 43 scalar modules from
the inequality/negation checkpoint. The full group was used because shared
scalar extraction changed. The fixed arithmetic archive and unrelated runtime
suite were not rebuilt; affected general proof and type validation modules
used cached dependencies.

Two-argument functions in this increment return UInt64 or Id UInt64. Functions
with two UInt64 arguments returning ForInStep remain the next capability.
