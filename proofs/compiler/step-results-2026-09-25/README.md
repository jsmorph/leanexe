# Loop-step result bindings and nested Id computations

Candidate `317cbb8b` adds typed ForInStep UInt64 result bindings to loop bodies:
ordinary lets, aliases, lexical captures and straight-line standard Id monadic
binds. Id.run and pure can wrap a computed result. The source model retains
arbitrary nested Id result annotations and both compiled projections describe
the same native step value. Every bound computation is checked, including an
unused result. A computed done value exits only when returned by the callback.

Both final commands exited 0 using pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: complete compiler correctness, exact bytes,
  full module validation and exported execution, with all nine axiom audits.
- `tools/arithmetic-check.js range-engine`: source admission, reserved exports,
  and 985 matching native Lean/V8 results across forty-two range declarations.

Eight new fixtures cover nested Id.run, pure wrapping a conditional result,
let aliases, captured results, monadic aliases, Id-typed lets, ignored done
values and multiple Id layers on bound results. All 192 focused native Lean/IR
comparisons passed. Public admission rejects unused unsupported result values,
unused unsupported monadic computations and custom Pure/Bind evidence.

All forty-two exact modules and expected results are retained; verification.json
records sizes and SHA-256 hashes. All thirty-four preceding modules are
byte-for-byte unchanged. The full seventy-six-declaration suite is configured
for 1,422 results; this increment ran the focused range group. The fixed
arithmetic archive and unrelated runtime/type-safety suite were not rebuilt.
Affected general compiler proof dependencies, including type validation, passed
using cached imports.

The first focused attempt exposed additional Id annotations produced by ordinary
inference. The checked ResultAnnotation model and recursive recognizer now cover
them. A branching monadic bind also exposed a generated local continuation with
a ForInStep argument. That function domain remains the next increment; the
current monadic fixture uses a pure conditional result followed by straight-line
bindings. The original fixture, both failures and inspected expressions are
retained. This increment does not add general elimination of ForInStep values,
new function domains, additional accumulators or multiple loops.
