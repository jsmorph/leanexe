# Mixed Boolean and propositional guards

Candidate `cf104d36` admits Boolean compounds inside propositional conjunction,
disjunction and negation, including repeated negation at either layer. Guard
nodes retain separate counts for Bool.not and propositional Not. Shared source
definitions avoid cyclic imports, and the independently checked Boolean guard
compiler supplies acceptance, operand success, native correctness and invariant
preservation to the enclosing propositional guard compiler.

The recognizer checks every subtree's source shape and the complete standard
decision expression. The common public source/step interface remains unchanged;
all branches and operands are checked, including unused helper bodies. Lowering
uses the same comparison and Boolean-word operations as before, with no backend
or runtime implementation change.

Both final commands exited 0 using pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: complete compiler correctness, exact bytes,
  full module validation and exported execution, with all nine axiom audits.
- `tools/arithmetic-check.js engine`: admission, reserved exports and 4,866
  matching native Lean/V8 results across all 247 declarations.

Eight new pure declarations cover mixed And/Or truth tables, propositional Not
over Boolean compounds, repeated negation, nested groups, zero divisors,
captures, binary functions, monadic joins and conditional operands. Four range
declarations cover break, continue, mutable branch updates, binary step helpers
and result-taking continuations. All 208 focused native Lean/IR comparisons and
three rejection tests passed. Custom BEq, custom inner decision evidence under
standard And evidence, and custom instances in unused bodies remain rejected.

All 247 exact modules and native expected results are retained with sizes and
SHA-256 hashes in verification.json. All 235 prior modules retained identical
bytes. General type validation used cached dependencies; the fixed arithmetic
archive and unrelated runtime suite were not rebuilt. General Boolean variables
and results, plus Boolean/Prop literals, remain later increments.
