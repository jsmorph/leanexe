# Word bindings inside Boolean expressions

Candidate `2477b2bbbfcbacfae23ae5f725e1b36075013fe7` supports exact `let name : UInt64 := value; body`
expressions producing admitted Boolean values. Word and flag bindings can nest,
shadow and capture each other. Word values may contain admitted scalar helpers,
Id computations and conditionals. Boolean results compose through conversions,
Id bindings, helper arguments, loop conditions, bounds and surrounding code.
Bound values are checked even when unused; both letE annotation flags are retained.

The source form keeps exact binding syntax and wraps body scalar operands in
their original word scope. External Boolean indices shift past the word slot.
Source variable typing now also requires recursive scope validity: word-bound
slots cannot be used as direct Boolean references, including through nested
bindings or branches. The lowerer enforces that condition and successful
compilation proves it. Lookup, size, parser reconstruction, completeness,
totality, semantics and invariants are kernel checked. Existing pure scalar
lowering handles word operands; pure bound computations can repeat. No emitter,
runtime or local-slot change was needed.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: all nine audits, including complete module
  type validation, exact bytes and terminating source-equal exported execution.
- `tools/arithmetic-check.js subset-engine boolean-word-let`: admission, reserved
  exports and 623 native Lean/V8 comparisons across 34 declarations.

The first focused fixture passed 304 native/IR comparisons, four declaration
rejections and 64 raw expression rejections. Cases cover mixed/nested bindings,
shadowing, captures, unused values, dependent choices, helpers in bound scalar
values, Id binds, negation, joined updates, continue/break, bounds and step helpers.
Wrong types/universes, unsupported unused/inactive computations, missing variables,
word-as-flag and flag-as-word reads are rejected. Nested bindings and choices
exercise the recursive scope condition in both scalar and step paths.

The preceding `boolLetUnsupportedType` body is now a positive case named
`boolWordLetOriginal`, unchanged apart from that name. It is included among the
eight new scalar declarations, without duplicating its old admission declaration.
The preceding Boolean-let fixture was updated to promote that body and four raw
word-let shapes. It now passes 318 native/IR comparisons, three declaration
rejections and 36 raw rejections. Its exact before/after sources are retained.
The prior dependent-choice fixture passes unchanged with 304 comparisons and
76 rejections. All five original inspected examples compile unchanged and their
bodies match focused, admission and native fixtures.

Eighteen selected prior modules have identical bytes. Emitted modules, native
results, sizes and SHA-256 hashes are retained. The full corpus has 600
declarations; this was a focused 34-declaration execution run. The last full
259-declaration evidence remains in ../extrema-2026-09-25. Cached dependencies,
the fixed arithmetic archive and unrelated runtime suite were reused. Broader
binding annotations, Boolean-returning helpers, Boolean public ABI, mixed
Bool/word helper parameters, broader saved-flag propositions and loops inside
helpers remain later capabilities.
