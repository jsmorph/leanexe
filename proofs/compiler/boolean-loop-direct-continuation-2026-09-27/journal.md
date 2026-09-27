# Direct local calls containing Boolean-result loops

The existing scalar predicate helper path remains first. A direct-call fallback
checks an argument outside the helper binding, then extracts the helper body with
that argument bound as a word or Boolean. The parser removes the helper binder
only when the argument cannot refer to it, preserving outer references.
The source constructors describe local application independently of extraction.
Their totality follows from argument totality and recursive body evaluation.

The shared continuation helper keeps scalar helper checks separate from direct
application checks and exposes acceptance and success lemmas. The first source
and parser builds pass. The first extraction edit left two old match branches
behind; these were removed. The scalar acceptance lemma also needed explicit
Boolean-mode parameters. The next extraction build passes, including source
support recovery. Correctness needed explicit unfolding of the two small binding
constructors in kind equalities; evaluation and invariant proofs then pass.
No new axioms or admitted proofs are used.

Ten native fixtures cover word and Boolean arguments, nested direct calls,
captured word/Boolean helpers, break/continue, stride and repeated Id annotations.
Raw syntax checks cover direct and public extraction, all four binder forms,
parameter ordering, Id domains/results, scalar and mixed conditional bodies,
argument capture, invalid domains/results, self-reference and unsupported bodies.
The all-scalar condition checks that fallback follows failure of the entire
existing helper path, including failure in its enclosing call body.

The public extraction and WASM-admission builds pass. Nine initial native cases
passed before the Id case exposed `Id.run (run argument)` around a local call.
That failed file is retained. The direct-call fixture now uses the same annotated
function and argument without that extra call wrapper; all ten cases pass 240
comparisons. Wrapper support is the next capability, before conditional `do`
continuations. Raw tests pass 16,128 native/IR comparisons, 5,760 invalid-input
checks and 576 equivalent-binding controls, including direct range extraction
of both-scalar conditional bodies. Prior predicate-helper and mixed-condition
syntax tests also pass, preserving scalar helper priority.

The complete compiler proof and nineteen axiom audits pass. Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1246 declarations.
