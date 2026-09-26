# Positive literal range strides

Candidate `a98a6517` adds standard positive Nat literal steps smaller than 2^64,
as in `[first:stop:2]`. Start and stop retain the earlier literal/dynamic rules.
The proof connects native strided List/range traversal to a zero-based loop
with a scaled index. Its ceiling-divided iteration count is bounded by the
natural distance. Word lowering uses `(distance - 1) / stride + 1` for nonempty
ranges, so adding the stride cannot overflow the computation.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: complete general compiler correctness,
  exact bytes, full module validation and execution, with all nine axiom audits.
- `tools/arithmetic-check.js range-engine`: admission, reserved exports and
  2,017 matching native Lean/V8 results across eighty-five range declarations.

All 288 focused native Lean/IR comparisons passed across twelve new fixtures:
uneven distances, dynamic endpoints, captured initial accumulators, high
indices, empty ranges, maximal steps, huge intervals with immediate exits,
continue, joined step-result binds and an explicit unit step. Overflowing and
custom literals, dynamic steps and a direct zero-step parser input reject.
The preceding nonunit-step rejection is now an accepted admission fixture.

The positivity expression is retained verbatim, including the generated proof
names shown in source-shapes.log. Independently checked numeric positivity and
size determine acceptance; an erased proof cannot override those checks. The
initial focused test log records a layout syntax error in a negative fixture.
The file was corrected and rerun successfully before committing the candidate.

All eighty-five exact modules and native expected results are retained with
sizes and hashes in verification.json. All seventy-three preceding range
modules retained identical bytes. The full 128-declaration/2,580-result group
remains configured; this increment ran the range group. The fixed arithmetic
archive and unrelated runtime suite were not rebuilt; affected general proof
and type validation modules used cached dependencies.
