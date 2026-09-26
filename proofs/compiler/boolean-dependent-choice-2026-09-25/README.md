# Dependent conditionals producing Boolean results

Candidate `ba0b0f70f68e7d048867d9d4976485c5e2152f7d` supports Boolean results from `if h : … then … else …`
over admitted Boolean equality, inequality and truth conditions, and closed
propositional guards. Both branches can contain saved flags, comparisons,
decisions and nested choices. Scalar/Id bindings, captures, helper calls, loop
steps, bounds and surrounding computations compose with the new results.

ExprProofBinder structurally inserts and removes an unused proof binder through
all Lean expression constructors, preserving names, types, annotations, metadata
and nested scopes. Kernel-checked inverse and size lemmas justify recursive
parsing. The parser checks exact proof domains and standard decision evidence,
rejects proof references, and reconstructs the exact original expression. The
independent native test matched Lean's own lifting and occurrence operations at
4,452 binder positions: 3,987 successful removals matched native lowering and
465 proof references rejected. These execution checks do not supply axioms to
the compiler theorem. New Boolean source forms share the existing proved
selection lowering. No emitter or runtime change was needed.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: all nine audits, including complete module
  type validation, exact bytes and terminating source-equal exported execution.
- `tools/arithmetic-check.js subset-engine boolean-dependent-choice`: admission,
  reserved exports and 623 native Lean/V8 comparisons across 34 declarations.

The first focused fixture passed 304 native/IR comparisons, four declaration
rejections and 72 raw expression rejections. Cases include nested proof scopes,
literal propositions, Bool truth/Eq/Ne, word comparisons, Id binds, unused valid
bindings, lexical captures through nested scalar helpers, joined loop updates,
continue/break, strided bounds and step-result helpers. Invalid decision
evidence, proof domains, branch/operand/binding types, universe levels and proof
reads are rejected, including unsupported inactive or unused branches. Both
scalar and step paths are checked. The preceding ordinary relation-choice and
dependent-condition fixtures passed unchanged: each has 304 comparisons, with
44 and ten rejection checks respectively.

All five original inspected examples now compile unchanged and their bodies
match the focused, admission and native-result fixtures. Exact inspected source
and before/after logs are retained. Eighteen selected prior modules have identical
bytes. Emitted modules, native results, sizes and SHA-256 hashes are retained.
The complete corpus contains 568 declarations; this was a focused 34-declaration
execution run. The last full 259-declaration execution evidence remains in
../extrema-2026-09-25. Cached dependencies, the fixed arithmetic archive and
unrelated runtime suite were reused. Boolean-returning helpers, Boolean public
ABI, mixed Bool/word helper parameters, broader saved-flag propositions and
loops inside helpers remain later capabilities.
