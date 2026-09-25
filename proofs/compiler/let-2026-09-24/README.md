# Pure UInt64 let bindings

Candidate `d777caf2` extends the general compiler theorem to strict source let
bindings over the pure, total UInt64 arithmetic grammar. It covers nested
bindings, shadowing, unused bindings and zero-argument declarations. Production
extraction substitutes compiled expressions for source variables; evaluation
remains strict in the source model, and the preservation theorem proves the
same result. This can repeat computation or expand emitted code. Heap/effectful
bindings and bindings of other types are outside this increment.

The pinned local environment is unchanged from the arithmetic milestone:
Lean 4.34.0-rc2 (`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0,
macOS arm64, authorized local `tools/leanrun` execution with the shared serial
lock. Both commands exited 0:

- `tools/arithmetic-check.js proof`: all affected proof dependencies checked,
  final general source/byte/export/invocation theorem passed, nine axiom audits.
- `tools/arithmetic-check.js engine`: actual native compiler, admission and
  reserved-export checks, twelve emitted modules, 142 matching native-Lean/V8
  results. Five new modules exercise binding cases over the existing fourteen
  edge-case pairs plus a bound constant.

The retained logs, native expected results and five new emitted modules record
these checks. The existing arithmetic archive remains a fixed separately
verified checkpoint. No type-safety implementation changed, so its successful
438-theorem audit was not repeated. Unrelated runtime suites were not rebuilt.

`tools/leanrun --timeout 60 lake env lean test/scalar_class_evidence.lean`
also exited 0, checking standard/custom operator and literal instances through
the production compiler against native source evaluation (`class-evidence.log`).
