# Dynamic range starts

Candidate `ce8443b8` adds starts expressed as supported UInt64 expressions
followed by `.toNat`, including `[first.toNat:stop.toNat]`. Both endpoints use
the same checked source model, retaining exact Nat values. The checked native
interval and index-shift connection reuses the four-local early-exit backend.
The lowering avoids subtraction wrap and proves that captured start values
remain unchanged by accumulator updates.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: complete general compiler correctness,
  exact bytes, module validation and execution, with all nine axiom audits.
- `tools/arithmetic-check.js range-engine`: admission, reserved exports and
  1,729 matching native Lean/V8 results across seventy-three range declarations.

All 264 focused native Lean/IR comparisons passed across eleven new fixtures:
computed and conditional starts, literal and dynamic stops, captured initial
accumulators, high indices, empty/equal/reversed bounds, huge intervals with
immediate exits, continue and result joins. General Nat arithmetic and calls
to unsupported top-level helpers in starts reject. The earlier dynamic-start
rejection is now an explicit accepted source-admission test; literal overflow
and custom-instance rejection tests remain.

All seventy-three exact modules and expected results are retained with sizes
and hashes in verification.json. All sixty-two preceding range modules retained
identical bytes. The full 116-declaration/2,292-result execution group remains
configured; this increment ran the range group. The fixed arithmetic archive
and unrelated runtime suite were not rebuilt; affected general proof and type
validation modules used cached dependencies.
