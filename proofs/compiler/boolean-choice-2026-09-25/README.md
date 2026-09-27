# Boolean-valued conditionals over Boolean guards

Candidate `27abf6a0` supports Boolean-valued choices in ordinary lets,
standard Id action leaves, helper captures and loop code. Conditions and both
arms may contain saved Boolean values, standard UInt64 ==/!= expressions,
literals, junctions, negations and nested choices. Choices also work directly
as scalar and step conditions, including when they contain no saved flag.
The source grammar preserves exact ite Bool syntax and standard Bool decision
evidence. Parser acceptance/reconstruction and operand-size proofs cover the
new form. Shared lowering uses the existing word conditional, Boolean zero/one
representation and comparison. Both branches and every operand are checked.

The Boolean condition routing predicate now identifies either local variables
or choices. Its exclusion proofs keep all previous closed guards on their
existing path. Scalar, step and outer-loop source semantics, totality and
extraction proofs reuse the shared interface without changing the emitter.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: all nine audits, including complete module
  type validation, exact bytes and terminating source-equal exported execution.
- `tools/arithmetic-check.js subset-engine boolean-choice`: admission,
  reserved exports and 623 native Lean/V8 comparisons across 34 declarations.

All 304 focused native/IR comparisons pass across eight pure and eight range
cases. Cases cover nested choices, repeated negation, shadowing, helper captures,
dependent outer conditions, joined do updates, monadic Boolean bindings, unused
values, break/continue, strided bounds and choices before/after a loop. Four
source rejections and eight raw choice rejections cover unsupported inactive
or unused arms, custom/mismatched decision evidence and wrong result/arm types.
The prior Boolean-local and dependent-Boolean focused files also pass unchanged:
608 native/IR comparisons and 18 rejection checks, including binding kinds and
proof-binder scope. Logs are retained beside the new cases.

This increment covers Boolean guards on Boolean-valued choices. Propositional
guards such as x < y inside these choices, and conditional Id actions, remain
separate capabilities. No emitter/runtime code changed. All selected modules,
expected results and logs are retained with sizes and SHA-256 hashes in
verification.json. Eighteen selected preceding modules kept identical bytes.
This focused run checks 34 declarations; the complete corpus contains 423.
The last full 259-declaration execution evidence remains in
../extrema-2026-09-25. Cached dependencies were reused with bounded affected
builds. The fixed arithmetic archive and unrelated runtime suite were not rebuilt.
