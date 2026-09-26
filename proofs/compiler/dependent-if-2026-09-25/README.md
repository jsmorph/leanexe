# Dependent conditionals

Candidate `7d9535a3` admits `if h : condition then ... else ...` over
all previously supported guard trees, with scalar and complete step results.
The shared parser checks the standard decision expression, true proof domain
and negated false proof domain exactly. An erased binder remains in each branch
context so outer variables, index/accumulator positions and helper captures keep
their lexical meaning. Both branches and all guard operands are checked.

Independent source support and total semantics, extraction acceptance and
successful-extraction support, correctness and scalar/step output invariants
cover the new form. The general compiler theorem includes complete module type
validation, exact emitted bytes and terminating source-equal invocation. Proofs
are not executable words; additional proof-dependent runtime operations remain
outside the source grammar. No backend or runtime operation changed.

Both final commands exited 0 using pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: all nine compiler axiom audits passed.
- `tools/arithmetic-check.js subset-engine dependent-if`: admission, reserved
  exports and 623 matching native Lean/V8 results across 34 declarations.

Eight pure cases cover comparisons, compound/mixed/literal guards, nesting,
shadowing/captures, do-block joins, operands and finite-arity Id helpers. Eight
range cases cover yielding, early stopping, continue, joined updates, complete
step functions, step-result bindings, computed bounds/strides and outer helpers.
All 304 focused native Lean/IR comparisons pass. Four declaration rejection
cases cover custom decisions and unsupported inactive/unused bodies. Four raw
syntax cases reject wrong true/false proof domains for both scalar and step
results. An initial fixture inferred a Nat start; adding its intended UInt64
annotation fixed that fixture. Its failure log is retained.

All 34 tested modules and expected results are retained, with sizes and SHA-256
hashes in verification.json. Eighteen selected preceding modules kept identical
bytes. This was a focused execution run; the full corpus contains 335 declarations.
The preceding full 259-declaration execution evidence remains in
../extrema-2026-09-25. Type validation used cached dependencies. The fixed
arithmetic archive and unrelated runtime suite were not rebuilt.
