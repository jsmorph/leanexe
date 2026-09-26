# Propositional Boolean equality and inequality guards

Candidate `d4b102bae265fb7edfa274dbec28e7720eb2d448` supports scalar and step conditionals with propositional
Boolean `=` and `≠`, including dependent branches. Both sides may contain
admitted saved flags, comparisons, decisions, literals, junctions, negation,
Boolean equality and Boolean-valued choices. An indexed condition form retains
the exact Eq/Ne syntax and standard decision evidence while using the Boolean
equality meaning already proved. Eq with literal true on the right keeps the
existing truth-condition path. Parser acceptance, reconstruction, size bounds
and separation proofs connect the new forms to the existing scalar and loop
correctness, type and invariant proofs.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: all nine audits, including complete module
  type validation, exact bytes and terminating source-equal exported execution.
- `tools/arithmetic-check.js subset-engine boolean-proposition`: admission,
  reserved exports and 623 native Lean/V8 comparisons across 34 declarations.

All 304 focused native/IR comparisons, four source rejection tests and forty
raw guard rejection tests passed. Cases cover Eq/Ne truth cases, literal-true
path preservation, nested Boolean operands, ordinary and dependent branches,
helper captures, joined Id updates, early returns, break/continue, strided
bounds, step-result helpers and post-loop choices. Unknown, mismatched or
custom decisions, unsupported/inactive branches, wrong operand/binding types,
wrong universes and incorrect proof-lambda domains are rejected. An erased
proof cannot be read as a UInt64 value. The prior equality, Boolean-local and
dependent fixtures each pass all 304 comparisons, with twenty, eight and ten
rejection checks respectively; the latter two only changed named guard
construction to use its default truth form.

Five original inspected declarations rejected before this increment and now
accept unchanged. Their source and both syntax logs are retained. Two initial
focused fixture failures came from leading `!` consuming a larger proposition
and causing an implicit `decide`; the final tests parenthesize the intended
Boolean operand. Both failure logs and the original elaborated source are
preserved for the next decide extension. This increment adds UInt64/step
conditionals; Boolean-result choices or decide over these new propositions
remain separate extensions. Public arguments/results remain UInt64.

No emitter/runtime or scalar/loop dispatch changes were needed. Eighteen
selected preceding modules have identical bytes. Emitted modules, native
results, sizes and SHA-256 hashes are retained. This focused run covers 34
declarations; the complete corpus contains 520. The last full 259-declaration
execution evidence remains in ../extrema-2026-09-25. Cached dependencies, the
fixed arithmetic archive and unrelated runtime suite were reused.
