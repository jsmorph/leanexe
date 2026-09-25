# Dependent conditions over saved Boolean values

Candidate `fec27059` adds `if h : flag then ... else ...` with aliases,
Boolean conjunction/disjunction/negation and standard comparisons. The parser
checks the exact standard decision evidence and both proof-lambda domains.
The independent source semantics keeps Boolean values distinct from words;
both branches retain an erased proof binder in their lexical environment.
Scalar and step extraction have totality, acceptance, successful-support,
correctness and invariant proofs. The existing lowering and emitter are reused.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0, and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: all nine audits, including complete module
  type validation, exact bytes and terminating source-equal exported execution.
- `tools/arithmetic-check.js subset-engine boolean-dependent`: admission,
  reserved exports and 623 native Lean/V8 comparisons across 34 declarations.

Eight pure and eight range cases cover aliases, repeated negation, shadowing,
captures, compound conditions, nested operands, unused values, finite-arity
helpers, joined do-block updates, yielding, break, continue and computed bounds.
All 304 focused native Lean/IR comparisons pass. Four declaration rejection
tests check unsupported inactive bodies, custom decisions and unused helpers.
Six raw syntax tests reject incorrect true/false proof domains and attempts to
read the erased proof binder as a word, for both scalar and step results.

All tested modules, native results and logs are retained. Sizes and SHA-256
hashes appear in verification.json. Eighteen selected preceding modules kept
identical bytes. This focused execution run checks 34 declarations; the corpus
contains 367. The preceding full 259-declaration execution evidence remains
in ../extrema-2026-09-25. Cached dependencies were reused; the fixed arithmetic
archive and unrelated runtime suite were not rebuilt.

The first test exposed a distinct unsupported elaboration: Lean wrapped the
literal 5's UInt64 instance in a let and proof lambda. Explicit UInt64.ofNat 5
also produced a Nat OfNat expression with borrowed-type metadata, a second
currently unsupported literal shape. Both failures and raw expressions are
retained. `unhandled-instance.lean` preserves the original helper. The final
positive helper binds the multiplier before entering the proof scope. Supporting
these elaborated numeric forms is the next increment; this checkpoint does not
claim arbitrary instance normalization.
