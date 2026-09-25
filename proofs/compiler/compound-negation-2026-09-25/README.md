# Negation of compound propositional guards

Candidate `1c6a528b` adds propositional Not around entire conjunctions and
disjunctions, including repeated negation and nesting at any level. Junction
nodes retain a count of their outer Not wrappers. Comparison leaves keep their
existing comparison negation descriptor, preserving unambiguous recognition.
The recognizer checks every standard instDecidableNot wrapper in the complete
decision expression, including the inner decisions.

Each wrapper lowers to equality between the preceding Boolean word and zero.
The checked lowering preserves native Boolean meaning and existing scalar
invariants. Zero wrappers retain exactly the previous junction output. The
public scalar and paired loop-step source rules and proofs reuse the shared
guard interface; no backend or runtime implementation changed.

Both final commands exited 0 using pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: complete compiler correctness, exact bytes,
  full module validation and exported execution, with all nine axiom audits.
- `tools/arithmetic-check.js engine`: admission, reserved exports and 4,450
  matching native Lean/V8 results across all 223 declarations.

Eight new pure declarations cover both negated truth tables, double/triple
negation, nested negated groups, zero divisors, captures, binary local functions,
monadic joins and nested conditional operands. Four range declarations cover
break, continue, mutable branch updates, binary step helpers and result-taking
continuations. All 208 focused native Lean/IR comparisons and three rejection
tests passed. Custom outer decisions, custom inner decisions under a standard
Not instance, and custom evidence in unused helper bodies remain rejected.

All 223 exact modules and native expected results are retained with sizes and
SHA-256 hashes in verification.json. All 211 prior modules retained identical
bytes. The full group was used because shared guard extraction changed.
General type validation used cached dependencies; the fixed arithmetic archive
and unrelated runtime suite were not rebuilt. Boolean &&/|| and general Boolean
values remain later coverage increments.
