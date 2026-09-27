# Nested Boolean Id operations

Candidate `44637199fc8f1c656e55aa9c408c6a156dd11210` supports standard Boolean `Id.run` and `pure` operations
at arbitrary recursive Boolean expression positions, with finite nested Id type
annotations. Exact standard instances, universe arguments and annotations remain
in the source syntax. Metadata is retained recursively. The native wrapper
semantics is definitionally the wrapped Boolean value; operands, variables and
scope conditions pass through it, with explicit outer negation.

Boolean actions now use this same recursive value representation. Compatibility
construction functions preserve their existing run/pure/metadata expressions.
This removes duplicate wrapper parsing while retaining all previously admitted
action forms. Checked size, parser reconstruction/acceptance, completeness,
scope, lowering correctness and invariants compose with the existing scalar,
step and range compiler proofs. Parser equations and induction are realized once
in the parser module; dependent-choice proofs use the specific equations instead
of repeatedly reducing the complete match. No emitter or runtime change.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: all nine audits, including complete module
  type validation, exact bytes and terminating source-equal exported execution.
- `tools/arithmetic-check.js subset-engine boolean-nested-id`: admission,
  reserved exports and 623 native Lean/V8 comparisons across 34 declarations.

The focused fixture passed 304 native/IR comparisons, four declaration rejection
tests and 160 raw wrapper rejection tests. Cases include nested Id types,
metadata, negation, operators, annotated bindings, shadowing, unused values,
captures, Boolean parameters, dependent choices, joined loop updates,
continue/break, strided bounds, step helpers and surrounding code. Wrong types,
universes and instance evidence are rejected, as are word values/slots read as
Boolean values through wrappers, including beneath a word let.

Five valid pre-implementation probes all rejected and now compile unchanged.
Their bodies match the focused, admission and native fixtures. The preceding
annotated-let and word-let fixtures pass unchanged with 304 comparisons each and
100/68 rejections. Eighteen selected prior modules retain identical bytes.
Emitted modules, native results, sizes and SHA-256 hashes are retained.
The full corpus has 632 declarations; this was a focused 34-declaration run.
The last full 259-declaration evidence remains in ../extrema-2026-09-25. Cached
dependencies, the fixed arithmetic archive and unrelated runtime suite were
reused. General Id-annotated scalar lets, Boolean-returning helpers, Boolean
public ABI, mixed Bool/word helper parameters, broader saved-flag propositions
and loops inside helpers remain later capabilities.
