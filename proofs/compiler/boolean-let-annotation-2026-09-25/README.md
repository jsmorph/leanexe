# Id annotations on bindings inside Boolean expressions

Candidate `1feb91fb1a24a6ebc86ef747a3d387891163352b` supports standard `Id Bool` and `Id UInt64` annotations,
including arbitrary finite nested Id layers, on let bindings inside admitted
Boolean expressions. Exact annotations, names and letE flags remain in the source
representation. Type-family parsers distinguish Boolean and word bindings and
check exact Id universe arguments and underlying types. Existing recursive scope
conditions prevent word slots from being used as flags.

Scalar operands generated from a binding use its underlying Bool or UInt64 type.
They preserve the same bound value, lexical scope and operand body. Checked size
lemmas show these underlying types fit beneath the original annotated expression;
source evaluation is proved independent of the Id annotation. This lets derived
operands reuse existing scalar let extraction. The original source annotation
is retained for parser reconstruction. Type-family disjointness, parser
acceptance/reconstruction, completeness, totality, lowering correctness and
invariants are kernel checked. Canonical arithmetic heads also admit standard Id layers on their result type;
inputs and full class-instance evidence remain exact UInt64 applications. The
head recognition and reconstruction theorems cover all ten word operations,
including uses outside these bindings. No emitter, runtime or local-slot change
was needed.
Pure bound computations may repeat in generated code.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: all nine audits, including complete module
  type validation, exact bytes and terminating source-equal exported execution.
- `tools/arithmetic-check.js subset-engine boolean-let-annotation`: admission,
  reserved exports and 623 native Lean/V8 comparisons across 34 declarations.

The focused fixture passed 304 native/IR comparisons, four declaration rejections
and 96 raw annotation rejections. Cases cover nested Id layers, mixed word/flag
bindings, shadowing, unused values, captures, scalar Id.run/pure computations,
negation, Id binds, joined loop updates, continue/break, strided bounds, step
helpers and surrounding code. Wrong Id/base universes, missing Id parameters,
unsupported base types, wrong bound/body types and nested word-as-flag reads are
rejected in scalar and step paths.

Two preliminary probe drafts had Lean elaboration errors and were corrected
before compiler implementation; their sources and logs are retained separately.
The five valid pre-implementation probes all rejected. The execution fixture exposed two gaps: generated scalar operands needed
underlying binding types, and Lean could put the nested Id annotation on an
arithmetic operation’s result type. Both failures and the second diagnostic
are retained. The fixture was unchanged after either failure; the source/lowering
and primitive-head corrections passed it. All ten word operations now recognize
these result annotations, retaining exact UInt64 inputs and standard instance
evidence. Another focused test passed 420 native/IR comparisons and 100 malformed
head rejections. All five valid original examples now
compile unchanged, with matching bodies across focused, admission and native
fixtures. Word values use explicit Id.run operations; Boolean uses follow the
admitted Boolean grammar.

The preceding word-let and Boolean-let fixtures pass unchanged with 304/318
comparisons and 68/39 rejections. Eighteen selected prior modules have identical
bytes. Emitted modules, native results, sizes and SHA-256 hashes are retained.
The full corpus has 616 declarations; this was a focused 34-declaration run.
The last full 259-declaration evidence remains in ../extrema-2026-09-25. Cached
dependencies, the fixed arithmetic archive and unrelated runtime suite were
reused. Nested Boolean Id operations, Boolean-returning helpers, Boolean public
ABI, mixed Bool/word helper parameters, broader saved-flag propositions and loops
inside helpers remain later capabilities.
