# Boolean-parameter helpers and conditional Boolean binds

Candidate `548ffaec` supports unary Bool-parameter local functions returning
UInt64 or ForInStep UInt64, including nested standard Id result annotations.
This covers the continuations Lean introduces for conditional Boolean binds:
`let flag ← if … then pure … else pure …`. These work in scalar computations,
loop steps, and scalar computations after a loop. Pure scalar Boolean helpers
can surround a loop and supply bounds, initial values and captured computations.

Separate Boolean-function kinds preserve the native Bool argument and its
proved zero/one IR representation. Source semantics and typed support cover
function bodies, calls and captures; totality and all four extraction proof
families extend through scalar, step and outer-loop code. Each helper body is
checked even when unused. Wrong domain types and attempts to read a Bool as a
word remain rejected. The scalar dispatch realizes its ordinary generated
induction theorem in its defining module with a local 300,000-heartbeat budget,
so importing proof modules reuse it. No axioms or native-evaluation oracle were
introduced.

The proof command passed on implementation candidate `8255840f`; the final
execution candidate changes only tests and task documentation. Both commands
exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: all nine audits, including complete module
  type validation, exact bytes and terminating source-equal exported execution.
- `tools/arithmetic-check.js subset-engine boolean-function`: admission,
  reserved exports and 647 native Lean/V8 comparisons across 35 declarations.

The focused fixture passes 328 native/IR comparisons over eight pure and nine
range programs, four declaration rejections and twelve malformed-helper checks.
It covers conditional binds, nested choices, direct Boolean arguments, local
capture and shadowing, nested helpers, annotated Id results, dependent branches,
unused bodies, loop break/continue and joined updates, helper-selected bounds,
step-valued helpers, and scalar work after a loop. The preceding propositional
choice fixture passes unchanged: 304 comparisons and twelve rejections.

Three original inspected conditional-bind declarations rejected before this
increment and now accept unchanged. Both syntax logs and their exact source
are retained. The new fixture first needed an explicit UInt64 annotation after
a nested Id result. A separate test used implicit Prop-to-Bool decide conversion;
that unsupported form was replaced by an explicit Boolean equality to test the
current helper grammar. Both failed fixture logs are retained. The original
three examples were not changed to bypass a rejection. The first execution gate
also exposed an old rejection expectation for an unused Bool → ForInStep helper.
That exact declaration is now an accepted test, included unchanged in all three
fixtures and in the native/V8 comparisons. Its first admission failure is retained.

Boolean public parameters/results, Boolean-returning helpers, mixed Bool/word
parameter lists, and loops inside helper bodies remain separate capabilities.
In particular, a conditional Boolean bind before a loop can elaborate to a
loop-containing helper. Explicit/implicit decide conversions are also a later
increment. No emitter/runtime code changed. All selected modules, expected
results and logs are retained with sizes and SHA-256 hashes in verification.json;
eighteen selected preceding modules are byte-identical. This focused run checks
35 declarations; the full corpus contains 456. The last full 259-declaration
execution evidence remains in ../extrema-2026-09-25. Cached dependencies were
reused; the fixed arithmetic archive and unrelated runtime suite were not rebuilt.
