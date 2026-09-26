# Local functions inside yielding range steps

Candidate `430802eb` admits direct local-function bindings inside a yielding
range body. The yield wrapper retains each binding's type and order; the
existing scalar extractor checks its value and continuation. Every function
body is checked, including unused functions. No backend or type representation
changed.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized local
serial `tools/leanrun` execution:

- `tools/arithmetic-check.js proof`: general source-to-exact-byte correctness,
  complete module validation/invocation and all nine axiom audits.
- `tools/arithmetic-check.js range-engine`: source admission, reserved exports,
  and 217 matching native Lean/V8 results across ten range declarations.

The three new modules cover index and accumulator captures, chained calls,
capture preservation after a later accumulator update, conditionals in local
functions and unused functions. Unsupported bodies and arities are rejection
cases. The fixed fixture list is shared by the driver and comparison checker;
missing declarations, missing input rows and duplicate inputs fail the check.
Native expected results and new module bytes are retained here.

The earlier range checkpoint retains the full 582-result run. This increment
reuses unchanged arithmetic coverage and checks all ten range cases. It does
not rebuild the fixed source archive or independent runtime/type-safety suites.
