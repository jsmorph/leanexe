# Local functions and branch continuations

Candidate `d73e047d` extends the general compiler theorem to local functions
with one UInt64 argument and UInt64 or Id UInt64 result. Lexical values now
distinguish words, Unit and the admitted function shapes internally. The public
parameter/result convention is unchanged. A local function captures its
surrounding bindings when defined; later shadowing cannot change those captures.
Functions may call previously defined local functions, contain arithmetic and
branches, and introduce additional local functions.

Compilation builds closures over compiled bindings and checks every function
body, including unused functions. Source evaluation and extraction are proved
for every admitted program. As with pure scalar lets, this substitutes pure
total computations and can repeat computation or expand emitted code.

The first execution attempt exposed the extra Unit parameter Lean introduces
for update continuations. The completed candidate explicitly distinguishes
`UInt64 → result` from `Unit → UInt64 → result`, requires literal Unit.unit at
such calls, and preserves both lexical scope and the carried scalar value.
Other multi-argument functions, function-valued parameters/results, top-level
helpers and loops are not part of this increment.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized local
serial `tools/leanrun` execution:

- `tools/arithmetic-check.js proof`: exact-byte correctness, full module
  validation, exported invocation and all nine axiom audits.
- `tools/arithmetic-check.js engine`: actual compiler admission/reserved-export
  checks and 437 matching native Lean/V8 results across thirty-four declarations.
  Seven new modules and all native expected results are retained here.

The final suite covers lexical shadowing, chained and nested functions, unused
functions, joined do branches and updates after branches. Unsupported function
bodies and other arities are checked as rejection cases. The initial failure is
retained alongside the completed execution log. Unchanged dependencies were
reused; the fixed arithmetic archive and independent type-safety/runtime suites
were not rebuilt.
