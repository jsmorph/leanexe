# Ordinary let bindings of range results

Candidate `e11f409a` admits an ordinary UInt64 let whose value is a range
computation and whose continuation is a supported scalar expression. The native
source relation evaluates the loop value before that continuation. Extraction
composes the plan's existing final-result expression with the continuation,
matching the earlier monadic-bind behavior. Nested lets, aliases, shadowing,
captured helpers and unused loop results are covered. Every loop value is checked,
including unused values. The instruction emitter and loop layout are unchanged.

Both final commands exited 0 using pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: complete compiler correctness, exact bytes,
  full module validation and exported execution, with all nine axiom audits.
- `tools/arithmetic-check.js range-engine`: admission, reserved exports and 2,977
  matching native Lean/V8 results across 125 range declarations.

Ten new declarations cover ordinary and explicit ForIn values, nested lets,
captures, aliases, unused results, stepped early exits, continue, monadic
continuations and local helpers before/after the loop. All 240 focused native
Lean/IR comparisons and three rejection tests passed. Unsupported unused loop
bodies, two separate loops and Boolean loop-result bindings remain rejected.
The last two remain later capabilities.

All 125 exact modules and native expected results are retained with sizes and
SHA-256 hashes in verification.json. All 115 prior range modules retained identical
bytes. General type validation passed using cached dependencies; the fixed
arithmetic archive and unrelated runtime suite were not rebuilt.
