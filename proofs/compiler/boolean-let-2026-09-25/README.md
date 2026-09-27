# Boolean bindings inside Boolean expressions

Candidate `d7368686cf2460c1797f660a3b577450d7499543` supports exact `let name : Bool := value; body`
expressions inside admitted Boolean values. Bindings can nest, shadow and capture
flags, and occur under negation, choices, decisions, conversions, Id bindings,
helper arguments, loop conditions and surrounding scalar computations. Bound
values are checked even when unused. Both flags on letE syntax are retained.

The source form records the original name, binding annotation, value and body.
Body flag index zero denotes the new value, while external flag indices shift
back into the surrounding context. Scalar operands from the body retain an
explicit copy of their original Boolean let scope. Thus a scalar conditional or
nested scalar helper can read the local flag without confusing it with a word
binding or an outer capture. Operand-size, parser reconstruction, typed-variable,
completeness, totality, lowering correctness and invariant proofs cover these
rules. This uses existing pure scalar lowering; compiled expressions can repeat
pure bound computations. No emitter, runtime or additional local-slot changes
were needed.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: all nine audits, including complete module
  type validation, exact bytes and terminating source-equal exported execution.
- `tools/arithmetic-check.js subset-engine boolean-let`: admission, reserved
  exports and 623 native Lean/V8 comparisons across 34 declarations.

The first focused fixture passed 304 native/IR comparisons, four declaration
rejections and forty raw expression rejections. Cases cover nested bindings,
shadowing, captures, unused values, scalar operands that read the bound flag,
nested scalar helpers, dependent choices, negation, Id binds, joined loop updates,
continue/break, strided bounds and step-result helpers. Wrong binding/value/body
types, invalid Bool universe arguments, out-of-range references, nested invalid
bindings, reading words as flags and reading flags as words are rejected in both
scalar and step code. Unsupported unused/inactive computations remain rejected.
The preceding dependent-choice and Boolean-local fixtures passed unchanged: each
has 304 comparisons, with 76 and eight rejection checks respectively.

All five original inspected examples now compile unchanged, with matching bodies
across focused, admission and native fixtures. Exact inspected source and
before/after logs are retained. Eighteen selected prior modules have identical
bytes. Emitted modules, native results, sizes and SHA-256 hashes are retained.
The complete corpus has 584 declarations; this was a focused 34-declaration run.
The last full 259-declaration execution evidence remains in ../extrema-2026-09-25.
Cached dependencies, the fixed arithmetic archive and unrelated runtime suite
were reused. Word bindings inside Boolean expressions, Boolean-returning helpers,
Boolean public ABI, mixed Bool/word helper parameters, broader saved-flag
propositions and loops inside helpers remain later capabilities.
