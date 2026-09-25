# Nonzero literal range starts

Candidate `6aa364fd` adds unit-step ranges such as `[3:8]` and
`[1:count.toNat]`. The standard Nat literal start must be smaller than 2^64;
stop bounds retain the existing literal or UInt64-expression rules. Native
interval iteration, truncated distance and index shifting are proved before
reusing the existing four-local early-exit backend. Empty intervals preserve
the initial accumulator; source indices retain their exact Nat meaning.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: complete general compiler correctness,
  exact module bytes, full validation and execution, with all nine axiom audits.
- `tools/arithmetic-check.js range-engine`: admission, reserved exports and
  1,465 matching native Lean/V8 results across sixty-two range declarations.

The eleven new fixtures cover dynamic and literal stops, equal and reversed
bounds, break/continue, captured helpers, joined step-result bindings, indices
close to 2^64, and immediate exit from a huge interval. All 264 focused native
Lean/IR comparisons passed. Overflowing literals, custom literal instances and
as-yet unsupported dynamic starts reject. An overflowing start rejects even
when the source range is empty.

All sixty-two exact modules and expected results are retained here, with hashes
and sizes in verification.json. All fifty-one preceding range modules retained
identical bytes. The full 105-declaration/2,028-result execution group remains
configured; this change ran the range group. The fixed arithmetic archive and
unrelated runtime suite were not rebuilt. The affected general proof, including
type validation, used cached dependencies.
