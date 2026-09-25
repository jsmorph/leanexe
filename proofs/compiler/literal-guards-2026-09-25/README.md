# Boolean and propositional literal guards

Candidate `73760621` admits `true`, `false`, `True` and `False` as whole
guards and leaves of mixed Boolean/propositional guard trees. Source descriptions
retain Boolean and propositional negation wrappers and exact standard decision
evidence. Literal results lower through word equality, using existing IR and
backend operations. Shared parser, acceptance, operand, correctness and invariant
proofs connect this extension to the general scalar/function/loop theorems.

Both branches remain checked even for constant conditions. Unsupported inactive
branches, custom decision expressions and unsupported unused helper bodies are
rejected. General Boolean parameters, results and bindings remain outside this
increment.

Both final commands exited 0 using pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: complete compiler correctness, exact bytes,
  full module validation and exported execution, with all nine axiom audits.
- `tools/arithmetic-check.js subset-engine guard-literals`: admission, reserved
  exports and 503 matching native Lean/V8 results across 29 declarations.

The fixed execution group contains twelve new declarations and seventeen
existing guard/helper/do/loop cases. Eight new pure declarations cover all four
literals, repeated negation, nested mixed guards, captured binary helpers and do
joins. Four new range declarations cover break, continue, result joins and
binary step helpers. All 208 focused native Lean/IR comparisons and three
rejection tests passed.

All 29 tested modules and their expected results are retained with sizes and
SHA-256 hashes in verification.json. The seventeen selected prior modules kept
identical bytes. This was a focused execution run, not a rerun of all 271
corpus declarations. The preceding full 259-declaration execution evidence is
retained in ../extrema-2026-09-25. General type validation used cached dependencies;
the fixed arithmetic archive and unrelated runtime suite were not rebuilt.
