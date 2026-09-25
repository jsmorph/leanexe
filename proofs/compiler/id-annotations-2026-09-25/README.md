# Retained scalar Id annotations

Candidate `4c8beae3` admits any finite number of Id layers around UInt64
in scalar result annotations and standard run/pure/bind operations. The recursive
ResultType description and its parser preserve these exact annotations. Bind
input, output and lambda parameter annotations are checked; the input and
parameter must match exactly. The source semantics carries the same UInt64
values, since these Id types are definitionally UInt64.

Scalar and loop source rules, totality, acceptance, correctness and invariants
share these wrapper descriptions. The extension covers conditional and helper
results, scalar computations inside steps, and computations before and after
loops. The backend and runtime operations are unchanged. Custom Pure/Bind
expressions and unsupported unused helper bodies remain rejected. Ordinary
let bindings and function argument declarations retain their concrete UInt64
syntax; this increment concerns monadic and result annotations.

Both final commands exited 0 using pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: complete compiler correctness, exact bytes,
  full module validation and exported execution, with all nine axiom audits.
- `tools/arithmetic-check.js subset-engine id-annotations`: admission, reserved
  exports and 471 matching native Lean/V8 results across 26 declarations.

The fixed execution group contains twelve new declarations and fourteen
existing helper/do/loop cases. Eight new pure declarations cover the retained
returned-Id-helper example, nested pure/run, bind input/output annotations,
conditional results, binary/PUnit helpers and unused bodies. Four new range
cases cover wrappers around loops, binds before and after a loop, and scalar
Id helpers within early-exit steps. All 208 focused native Lean/IR comparisons
and three rejection tests passed.

All 26 tested modules and expected results are retained with sizes and SHA-256
hashes in verification.json. The fourteen selected prior modules kept identical
bytes. This was a focused execution run; the full corpus now contains 295
declarations. The preceding full 259-declaration execution evidence remains in
../extrema-2026-09-25. General type validation used cached dependencies; the
fixed arithmetic archive and unrelated runtime suite were not rebuilt.
