# Ordinary Boolean locals

Candidate `f9d25355` admits ordinary Boolean lets and their use in
ordinary Boolean conditions. Right-hand sides include literals, aliases,
standard UInt64 equality/inequality and Boolean negation, conjunction and
disjunction. Independent syntax tracks Boolean variable indices separately
from scalar comparison operands. Exact reconstruction and standard decision
checks preserve the original expression. Conditions containing a saved Boolean
are proved disjoint from preceding closed guard paths.

Source and compiled binding kinds keep Booleans distinct from UInt64 values.
Compiled Boolean values are pure words with proved Bool.toUInt64 meaning;
ordinary word lookup cannot read them. Source totality, extraction acceptance,
successful-extraction support, correctness and output invariants cover scalar
lets/branches, helper captures, loop steps and Boolean lets before a loop.
Captured flags retain their defining values throughout later shadowing and
accumulator updates. All operands and unused values are checked. No backend
or runtime operation changed.

Both final commands exited 0 using pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: all nine compiler audits, including full
  module type validation, exact bytes and terminating exported execution.
- `tools/arithmetic-check.js subset-engine boolean-locals`: admission, reserved
  exports and 623 matching native Lean/V8 results across 34 declarations.

Eight pure cases cover aliases, repeated negation, shadowing, helper capture,
compound conditions, nested operands, unused bindings and do-block joins.
Eight range cases cover yielding, early stopping, continue, captures, joined
updates, outer bindings/helpers, computed bounds/strides and complete step
functions. All 304 focused native Lean/IR comparisons pass. Four declaration
rejection tests cover unsupported unused values, custom equality and unsupported
ignored operands. Four raw syntax tests reject Boolean-as-word, word-as-Boolean,
word-backed conditions and erased proof/unit binders used as Booleans.

All 34 tested modules and expected results are retained with sizes and SHA-256
hashes in verification.json. Eighteen selected preceding modules kept identical
bytes. This was a focused execution run; the full corpus contains 351 declarations.
The preceding full 259-declaration execution evidence remains in
../extrema-2026-09-25. Type validation used cached dependencies. The fixed
arithmetic archive and unrelated runtime suite were not rebuilt.

Monadic Boolean binds, Boolean parameters/results, and propositional/dependent
guards containing saved Boolean locals remain separate capabilities.
