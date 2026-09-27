# Finite-arity local scalar helpers

Candidate `e3e3f2a5` removes the two-argument limit on local scalar
helpers with concrete UInt64 parameters and scalar results, including retained
Id result annotations. One shared function-suffix parser describes every larger
arity, and one local-call parser and argument-list compiler preserve source
order, original type/body syntax and exact argument counts. Each closure keeps
its lexical captures. Bodies are checked even when unused, and every supplied
argument is checked even when its value is unused by the body.

Source totality, compiler acceptance, successful-extraction support, correctness
and output invariants cover scalar helper definitions and calls, definitions
inside loop steps, and helpers surrounding loops. Existing unary/binary and
Unit/PUnit continuations keep their preceding paths. Helpers returning complete
ForInStep results still have the preceding argument limits; partial applications,
function-valued parameters/results and top-level helper calls remain outside
this increment. Larger scalar calls inside yielding steps use the existing
plain-binding/yield conversion and the shared scalar extractor. No backend
emission or runtime operation changed.

Both final commands exited 0 using pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: complete compiler correctness, exact bytes,
  full module validation and exported execution, with all nine axiom audits.
- `tools/arithmetic-check.js subset-engine finite-arity`: admission, reserved
  exports and 571 matching native Lean/V8 results across 31 declarations.

The fixed execution group contains fourteen new declarations and seventeen
preceding helper/do/loop cases. Eight new pure declarations cover three, four,
five and six parameters, asymmetric argument order, lexical capture and
shadowing, nested/chained helpers, Id/do/conditional results and unused bodies.
Six range cases cover yielding and early-exit steps, guards, literal strides,
loop bounds, outer captures and pure computations after loops.
All 256 focused native Lean/IR comparisons pass. Four declaration rejection
tests cover unsupported unused bodies, wrong parameter types, partial
application and an unsupported ignored operand. Two raw syntax tests check
insufficient/excessive argument counts. The updated preceding helper test also
passes 140 comparisons and three rejection tests; its former three-argument
rejection is now a positive case. The preceding outer-helper test passes 264
comparisons and three rejection tests after the equivalent outer helper was
moved from rejection to positive coverage. The first admission attempt exposed
that stale expectation; its failure log is retained. The general audit used
commit 7800bcd6; the final candidate changes only these test expectations and
status notes, with identical compiler/proof sources.

All 31 tested modules and expected results are retained with sizes and SHA-256
hashes in verification.json. The seventeen selected prior modules kept identical
bytes. This was a focused execution run; the full corpus now contains 309
declarations. The preceding full 259-declaration execution evidence remains in
../extrema-2026-09-25. General type validation used cached dependencies; the
fixed arithmetic archive and unrelated runtime suite were not rebuilt.
