# Local scalar helpers defined before range loops

Candidate `01d0c335` admits unary UInt64, binary UInt64 and Unit-prefixed scalar
helpers surrounding a range loop. Helpers return UInt64 or Id UInt64 and may
appear in endpoints, the initial accumulator, loop steps and the final result.
They retain their original lexical captures across later shadowing and mutable
updates. The source grammar, extraction, acceptance, preservation and invariants
reuse the existing function bindings and scalar body proofs. The pointwise
captured-environment relation holds for every accumulator, index, stop and exit
flag. All bodies are checked, including unused helpers. The emitter is unchanged.

Both final commands exited 0 using pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: complete compiler correctness, exact bytes,
  full module validation and exported execution, with all nine axiom audits.
- `tools/arithmetic-check.js range-engine`: admission, reserved exports and 2,737
  matching native Lean/V8 results across 115 range declarations.

Ten new declarations cover all three argument forms, capture across shadowing,
computed bounds and initial values, chained/nested helpers, monadic bodies and
calls, unused functions, continue/break and calls from binary step-result helpers.
All 240 focused native Lean/IR comparisons and four rejection tests passed.
Unsupported unused bodies, three-argument helpers, Nat domains and partial
application remain rejected.

All 115 exact modules and native expected results are retained with sizes and
SHA-256 hashes in verification.json. All 105 prior range modules retained identical
bytes. General type validation passed using cached dependencies; the fixed
arithmetic archive and unrelated runtime suite were not rebuilt.
