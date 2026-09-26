# Bool.toUInt64 conversions

Candidate `cdfe21b4` supports Bool.toUInt64 applied to admitted Boolean values:
literals, saved flags, comparison/decision results, negation, junctions and
nested choices. Dot notation and direct calls retain the same exact source
head. The scalar source grammar records native Bool.toUInt64 meaning and typed
Boolean references; acceptance and totality require all input operands to be
supported. The compiler reuses guardWord and its proved zero/one representation.
All four scalar proofs are extended; step and surrounding-loop proof modules
reuse the scalar interface without further changes.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: all nine audits, including complete module
  type validation, exact bytes and terminating source-equal exported execution.
- `tools/arithmetic-check.js subset-engine boolean-word`: admission, reserved
  exports and 623 native Lean/V8 comparisons across 34 declarations.

All 304 focused native/IR comparisons, four source rejections and thirteen raw
conversion rejections passed on the first fixture run. Cases cover literal,
direct and dot syntax, captures/shadowing, nested converted comparison operands,
ordinary/dependent conditions, conditional Id binds, helper arguments, unused
values, loop break/continue, joined updates, converted bounds/initial values,
step-result helpers and post-loop arithmetic. Wrong input types, word bindings
used as Boolean values, free variables, wrong universe levels and unsupported
operands are rejected even when unused. The preceding decide fixture passes
unchanged: 304 comparisons and twelve rejection checks.

Four original inspected declarations rejected before this increment and now
accept unchanged. Their source and both syntax logs are retained. The public
ABI remains UInt64; this increment converts internally computed Boolean values.
Boolean-returning helpers and unsupported Boolean inputs are not admitted by
the conversion. No emitter/runtime code changed. Eighteen selected preceding
modules are byte-identical; emitted modules, native results, sizes and SHA-256
hashes are retained. This focused run covers 34 declarations; the complete
corpus contains 488. The last full 259-declaration execution evidence remains
in ../extrema-2026-09-25. Cached dependencies, the fixed arithmetic archive and
unrelated runtime suite were reused.
