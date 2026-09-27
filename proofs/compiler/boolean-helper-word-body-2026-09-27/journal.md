# General predicate bodies before scalar word continuations

Ten fixed native probes fail before this change: repeated word/Boolean helper
calls, unused helpers, captured predicates, a proposition let, an Id body and
four range programs whose scalar guard or tail operands use these helpers.

The two ordinary scalar predicate-binding rules now retain raw Lean expressions.
Their evaluation and support premises still recursively check the Bool.toUInt64
conversion of the body. The scalar parser keeps its exact function-domain,
lambda-domain and Boolean result checks, validates an unused body at zero, and
constructs the same typed predicate closure. It no longer requires a prior
BooleanLocal body parse. The equation and source proof arguments preserve the
same checked conversion. The separate loop-step and outer-loop helper parsers
are unchanged in this capability.

Removing two impossible parse-failure cases changes the functional induction
case indices. The support proof is adjusted to use each raw body and its existing
recursive hypothesis. The generated induction signature is checked against that
mapping after building the core. Existing step/range proofs may need explicit
raw body projections when applying the generalized scalar equations.

The focused source/core target passes on its first run (136 targets), as does
the scalar proof target (137 targets). The generated functional induction cases
match the revised support proof: raw body branches are 50 and 59. The public
compiler dependencies are next.

The public compiler target passes (196 targets) without additional loop-proof
edits. All ten new probes now pass unchanged. The original proposition-let probe
also passes, with its three converted-helper controls still passing; Id inputs
remain rejected in that fixed probe. New tests pass 88,884 comparisons, 95,152
invalid-input checks and 1,728 controls. All passed on their first runs. The final
scalar syntax run adds exact count assertions and removes an unused test binder.

The next six loop probes distinguish existing scalar paths from the dedicated
step/outer parsers. Word-body updates, unused step helpers and a word-input
continue example already pass through the broader scalar path. A Boolean-input
helper before break and both outer-loop helper examples remain rejected. These
measured results determine the next step scope; no blanket loop-body claim is
made from the scalar change.

Prior tests pass 66,888 comparisons, 48,400 invalid-input checks and 2,048 controls.

The general compiler proof and nineteen axiom audits pass (3377 build targets). Passed 993 native Lean / independent Wasm engine comparisons across 54 declarations.
44 prior modules retain identical bytes; 0 changed. The full native corpus contains 1517 declarations. Prior tests pass 66888 comparisons, 48400 invalid-input checks and 2048 controls.
