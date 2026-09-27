# Mixed Boolean/word public parameters in scalar functions

This increment keeps the i64 parameter ABI. Zero decodes to false and every
nonzero input decodes to true for a Bool parameter; UInt64 parameters retain all
bits. Compiled Boolean bindings normalize to zero/one before being used by the
source body. The theorem therefore continues to quantify every exported i64
argument list without a hidden canonical-Boolean precondition.

The source public argument kinds, decoding and type-list agreement are added.
Source.Apply now carries typed local values. Existing word-only collection
lemmas preserve their premises and application behavior; a new typed collection
lemma evaluates the original term with decoded arguments. Source signatures
track Bool domains through the independent input-kind traversal. Word-parameter
range functions remain supported; Boolean-input loop functions are the following
increment after scalar functions are checked end to end.

The first foundational build needed an explicit List.replicate_succ rewrite in
the all-word decoding lemma. The corrected foundation and source application
proofs pass. No source-to-WASM or execution claim is made for this unfinished
increment yet. Typed compiled bindings and extraction integration are next.

The compiled binding proofs passed after fixing an untyped index binder and a
Lean continuation indentation error. Signature soundness is proved independently
by parser cases. Function extraction, source/IR evaluation, descriptor admission,
WASM execution, exact body bytes and validation then passed focused builds.

Review of Apply exposed a proof issue introduced by mixed inputs: word and
Boolean lambda constructors must not accept the same arbitrary annotation. The
constructors now require their exact respective types, and publicLambdasMatch
checks each lambda against the declared input list before extraction. This also
rejects malformed raw expressions with mismatched domains. A common typed
application lemma handles both word and Boolean inputs. Lean Expr's BEq is not a
structural equality proof, so annotation matching uses exact constructor patterns
with an independently proved type equality lemma.

The first native capture fixture combined a Bool-to-Bool helper inside a
UInt64-to-Bool helper body, which exceeds the current local predicate-body
recognizer. The fixture for this increment uses repeated Bool-to-Bool calls
capturing both public inputs. The original fixture is preserved in the scratch
definition file and should become a separate capability after public input work.
The initial raw syntax matrix passed 44,352 comparisons, 16,320 rejection checks
and 1,056 controls. Additional negative tests now check mismatched lambda types
and invalid lambda universes.

A diagnostic separated Boolean input binding from helper composition: helpers
capturing the flag, the word, or both compile correctly with a direct call.
A public Boolean result whose outer helper let has a junction of calls does not
yet pass the Boolean result-expression recognizer. The final capture fixture
uses a direct call with both captures. The diagnostic and both earlier failure
logs are retained. Expanding Boolean-result helper-let bodies is follow-up work;
this does not affect ordinary scalar bodies with explicit conversions.

The tightened lambda rules and extraction proof now pass. The type matcher uses
an exact syntactic pattern; unfolding and splitting that pattern gives the
required domain equality. The strengthened raw matrix passes 44,352 comparisons,
18,432 invalid-input checks and 1,056 result-conversion controls.

The final native fixture also exposed compound propositional Boolean equality
combined with a truth guard (`left = right ∨ ¬ left`) under a decision. This
combination is recorded for expansion separately; the current input increment
checks the existing atomic Boolean equality decision, including nested Id public
results. All nine prior test files pass, including public result annotations,
Boolean results, call arguments, input annotations and function rejection checks.

The general compiler theorem and nineteen audits pass. Native Lean/V8 agree on 439 inputs across 28 declarations, including six prior ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1086 declarations.
